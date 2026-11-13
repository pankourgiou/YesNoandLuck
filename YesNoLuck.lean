/-!
# YesNoLuck — a player who only receives YES/NO answers still plays luck games almost optimally.
Core Lean 4 only (tested on 4.15 and 4.24).  Everything lives in `namespace YesNoLuck`
so it cannot clash with Mathlib's `Dist`, `encode`, `decode`.
-/
namespace YesNoLuck

/-- our own `if`-lemmas, so no deprecated core names are needed -/
theorem ite_yes {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by simp [h]
theorem ite_no {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b := by simp [h]

theorem nn (n : Nat) : (0 : Int) ≤ (n : Int) := by omega

/-- one tactic for all the associativity/commutativity bookkeeping (a tactic "decorator") -/
macro "int_norm" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Int.pow_succ, Int.natCast_add, Int.natCast_one, Int.add_mul, Int.mul_add,
      Int.one_mul, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] $[$loc]?)

/-- send index `i` as `L` yes/no answers (least significant bit first) -/
@[simp] def encode : Nat → Nat → List Bool
  | 0, _ => []
  | L+1, i => (i % 2 == 1) :: encode L (i / 2)

/-- the player turns the answers back into a number -/
@[simp] def decode : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * decode bs

@[simp] theorem length_encode : ∀ L i, (encode L i).length = L := by
  intro L
  induction L with
  | zero => intro i; rfl
  | succ L ih => intro i; simp [encode, ih]

/-- no information is lost: decoding the answers returns the index -/
@[simp] theorem decode_encode : ∀ L i, i < 2 ^ L → decode (encode L i) = i := by
  intro L
  induction L with
  | zero => intro i h; simp at h; simp [encode, decode]; omega
  | succ L ih =>
    intro i h
    have h2 : i / 2 < 2 ^ L := by rw [Nat.pow_succ] at h; omega
    simp only [encode, decode, ih (i / 2) h2]
    by_cases hb : i % 2 = 1 <;> simp [hb] <;> omega

/-- any L answers decode to a number below 2^L -/
theorem decode_lt : ∀ bs : List Bool, decode bs < 2 ^ bs.length
  | [] => by simp [decode]
  | b :: bs => by
      have := decode_lt bs
      simp only [decode, List.length_cons, Nat.pow_succ]
      cases b <;> simp <;> omega

/-- the player plays exactly the advisor's best move (index i) when K ≤ 2^L -/
theorem player_plays_best {α : Type} (ms : List α) (i L : Nat)
    (hi : i < ms.length) (hL : ms.length ≤ 2 ^ L) :
    ms[decode (encode L i)]? = ms[i]? := by
  rw [decode_encode L i (Nat.lt_of_lt_of_le hi hL)]

/-- noise lemma: a wrong decode needs at least one flipped answer -/
theorem wrong_needs_a_flip (L i : Nat) (rx : List Bool) (h : i < 2 ^ L)
    (hne : decode rx ≠ i) : rx ≠ encode L i := by
  intro e; subst e; exact hne (decode_encode L i h)
/-! Weighted finite distributions with integer (unnormalised) expectation. -/
@[reducible] def WDist (β : Type) := List (Nat × β)

namespace WDist
@[specialize, simp] def E {β : Type} : WDist β → (β → Int) → Int
  | [], _ => 0
  | (w, x) :: d, f => (w : Int) * f x + E d f
@[simp] def mass {β : Type} : WDist β → Nat
  | [] => 0
  | (w, _) :: d => w + mass d
@[simp] def wt {β : Type} : WDist β → (β → Bool) → Nat
  | [], _ => 0
  | (w, x) :: d, P => (if P x then w else 0) + wt d P

theorem E_mono {β : Type} (d : WDist β) (f g : β → Int) (h : ∀ x, f x ≤ g x) : E d f ≤ E d g := by
  induction d with
  | nil => simp [E]
  | cons p d ih =>
    obtain ⟨w, x⟩ := p
    simp only [E]
    have := Int.mul_le_mul_of_nonneg_left (h x) (nn w)
    omega

@[simp] theorem E_const {β : Type} (d : WDist β) (c : Int) : E d (fun _ => c) = (d.mass : Int) * c := by
  induction d with
  | nil => simp [E, mass]
  | cons p d ih =>
    obtain ⟨w, x⟩ := p
    simp only [E, mass, ih, Int.natCast_add, Int.add_mul]

@[simp] theorem E_sub {β : Type} (d : WDist β) (f g : β → Int) : E d (fun x => f x - g x) = E d f - E d g := by
  induction d with
  | nil => simp [E]
  | cons p d ih =>
    obtain ⟨w, x⟩ := p
    simp only [E, ih, Int.mul_sub]
    omega

@[simp] theorem E_add {β : Type} (d : WDist β) (f g : β → Int) : E d (fun x => f x + g x) = E d f + E d g := by
  induction d with
  | nil => simp [E]
  | cons p d ih =>
    obtain ⟨w, x⟩ := p
    simp only [E, ih, Int.mul_add]
    omega

@[simp] theorem E_ite {β : Type} (d : WDist β) (P : β → Bool) (c : Int) :
    E d (fun x => if P x then c else 0) = (d.wt P : Int) * c := by
  induction d with
  | nil => simp [E, wt]
  | cons p d ih =>
    obtain ⟨w, x⟩ := p
    by_cases h : P x <;> simp [E, wt, h, ih, Int.add_mul]

theorem wt_or {β : Type} (d : WDist β) (P Q : β → Bool) :
    d.wt (fun x => P x || Q x) ≤ d.wt P + d.wt Q := by
  induction d with
  | nil => simp [wt]
  | cons p d ih =>
    obtain ⟨w, x⟩ := p
    by_cases hp : P x <;> by_cases hq : Q x <;> simp [wt, hp, hq] <;> omega

theorem wt_mono {β : Type} (d : WDist β) (P Q : β → Bool) (h : ∀ x, P x = true → Q x = true) :
    d.wt P ≤ d.wt Q := by
  induction d with
  | nil => simp [wt]
  | cons p d ih =>
    obtain ⟨w, x⟩ := p
    by_cases hp : P x
    · have := h x hp; simp [wt, hp, this]; omega
    · by_cases hq : Q x <;> simp [wt, hp, hq] <;> omega
end WDist

/-! ## Noise model: pattern `p k = true` means answer number `k` was flipped. -/
@[simp] def flipL : Nat → List Bool → (Nat → Bool) → List Bool
  | _, [], _ => []
  | k, b :: bs, p => Bool.xor b (p k) :: flipL (k + 1) bs p

theorem flipL_id : ∀ (bs : List Bool) (k : Nat) (p : Nat → Bool),
    (∀ j, k ≤ j → j < k + bs.length → p j = false) → flipL k bs p = bs := by
  intro bs
  induction bs with
  | nil => intro k p _; rfl
  | cons b bs ih =>
    intro k p h
    have h0 : p k = false := h k (Nat.le_refl k) (by simp only [List.length_cons]; omega)
    have h1 : flipL (k + 1) bs p = bs :=
      ih (k + 1) p (fun j hj hj2 => h j (by omega) (by simp only [List.length_cons]; omega))
    simp [flipL, h0, h1]

/-- the move the player ends up playing when the advisor meant index `i` and noise `p` hit -/
@[inline] def act (L i : Nat) (p : Nat → Bool) : Nat := decode (flipL 0 (encode L i) p)

/-- "some of the first L answers was flipped" -/
@[simp] def anyFlip : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | L + 1, p => anyFlip L p || p L

theorem anyFlip_false : ∀ (L : Nat) (p : Nat → Bool), anyFlip L p = false → ∀ j, j < L → p j = false := by
  intro L
  induction L with
  | zero => intro p _ j hj; omega
  | succ L ih =>
    intro p h j hj
    simp only [anyFlip, Bool.or_eq_false_iff] at h
    by_cases hjL : j = L
    · subst hjL; exact h.2
    · exact ih p h.1 j (by omega)

/-- no flipped answer ⇒ the player plays the advisor's move -/
theorem act_exact (L i : Nat) (p : Nat → Bool) (hi : i < 2 ^ L) (h : anyFlip L p = false) :
    act L i p = i := by
  unfold act
  rw [flipL_id (encode L i) 0 p (fun j _ hj => anyFlip_false L p h j (by rw [length_encode] at hj; omega))]
  exact decode_encode L i hi

theorem wt_false {β : Type} (d : WDist β) : d.wt (fun _ => false) = 0 := by
  induction d with
  | nil => simp [WDist.wt]
  | cons q d ih => obtain ⟨w, x⟩ := q; simp [WDist.wt, ih]

/-- UNION BOUND: if each answer is flipped with weight ≤ ew, some answer is flipped with weight ≤ L·ew -/
theorem union_bound (noise : WDist (Nat → Bool)) (ew : Nat) :
    ∀ L, (∀ k, k < L → noise.wt (fun p => p k) ≤ ew) → noise.wt (anyFlip L) ≤ L * ew := by
  intro L
  induction L with
  | zero => intro _; simp [anyFlip, wt_false]
  | succ L ih =>
    intro h
    have h1 := ih (fun k hk => h k (by omega))
    have h2 := WDist.wt_or noise (anyFlip L) (fun p => p L)
    have h3 := h L (by omega)
    show noise.wt (fun p => anyFlip L p || p L) ≤ (L + 1) * ew
    rw [Nat.add_mul, Nat.one_mul]; omega

/-! ## The luck game: a finite-horizon decision process against a FIXED opponent.
`tr s a` = weighted list of successor states (dice AND opponent replies live inside it).
Every number is an integer; an expectation is "unnormalised": each step multiplies the scale by the total mass.
The player's real result is the integer divided by `(M*W)^n`. -/

/-- value of the noisy yes/no player: the advisor's intended move is `idx n s`, the noise hits first -/
@[simp] def evalN {σ : Type} (tr : σ → Nat → WDist σ) (r : σ → Int) (idx : Nat → σ → Nat) (L : Nat)
    (noise : WDist (Nat → Bool)) : Nat → σ → Int
  | 0, s => r s
  | n + 1, s => noise.E (fun p => (tr s (act L (idx n s) p)).E (evalN tr r idx L noise n))

/-- the per-step error budget, solved: B(n+1) = (L·ew)·Δ·W·(MW)^n + MW·B(n) -/
@[simp] def Bd (Lew MW Δ W : Int) : Nat → Int
  | 0 => 0
  | n + 1 => Lew * (Δ * W * MW ^ n) + MW * Bd Lew MW Δ W n

theorem pow_nn (a : Int) (h : 0 ≤ a) : ∀ n : Nat, 0 ≤ a ^ n := by
  intro n
  induction n with
  | zero => rw [Int.pow_zero]; omega
  | succ n ih => rw [Int.pow_succ]; exact Int.mul_nonneg ih h

theorem perf_diff {σ : Type} (tr : σ → Nat → WDist σ) (r : σ → Int) (idx : Nat → σ → Nat) (L : Nat)
    (noise : WDist (Nat → Bool)) (M W ew : Nat) (Δ : Int) (hΔ : 0 ≤ Δ) (Vo : Nat → σ → Int)
    (hM : noise.mass = M) (hflip : ∀ k, k < L → noise.wt (fun p => p k) ≤ ew)
    (hW : ∀ s a, (tr s a).mass = W) (hidx : ∀ n s, idx n s < 2 ^ L)
    (hV0 : ∀ s, Vo 0 s = r s)
    (hVs : ∀ n s, Vo (n + 1) s = (M : Int) * (tr s (idx n s)).E (Vo n))
    (hgap : ∀ n s a, (tr s (idx n s)).E (Vo n) - (tr s a).E (Vo n) ≤ Δ * W * ((M : Int) * W) ^ n) :
    ∀ n s, Vo n s - evalN tr r idx L noise n s ≤ Bd ((L * ew : Nat) : Int) ((M : Int) * W) Δ W n := by
  intro n
  induction n with
  | zero => intro s; simp [hV0, evalN, Bd]
  | succ n ih =>
    intro s
    -- one decision costs at most W·B(n) after the continuation
    have hkey : ∀ a, (tr s a).E (Vo n) - (tr s a).E (evalN tr r idx L noise n)
        ≤ (W : Int) * Bd ((L * ew : Nat) : Int) ((M : Int) * W) Δ W n := by
      intro a
      rw [← WDist.E_sub]
      calc (tr s a).E (fun x => Vo n x - evalN tr r idx L noise n x)
          ≤ (tr s a).E (fun _ => Bd ((L * ew : Nat) : Int) ((M : Int) * W) Δ W n) :=
            WDist.E_mono _ _ _ (fun x => ih x)
        _ = (W : Int) * Bd ((L * ew : Nat) : Int) ((M : Int) * W) Δ W n := by
            rw [WDist.E_const, hW]
    -- pointwise bound for every noise pattern
    have hpt : ∀ p : Nat → Bool,
        (tr s (idx n s)).E (Vo n) - (tr s (act L (idx n s) p)).E (evalN tr r idx L noise n)
        ≤ (if anyFlip L p then Δ * W * ((M : Int) * W) ^ n else 0)
          + (W : Int) * Bd ((L * ew : Nat) : Int) ((M : Int) * W) Δ W n := by
      intro p
      have hk := hkey (act L (idx n s) p)
      have hg := hgap n s (act L (idx n s) p)
      by_cases hf : anyFlip L p = true
      · rw [ite_yes hf]; omega
      · have hf' : anyFlip L p = false := by simpa using hf
        have := act_exact L (idx n s) p (hidx n s) hf'
        rw [this] at hk ⊢
        rw [ite_no hf]; omega
    have hsplit : Vo (n + 1) s - evalN tr r idx L noise (n + 1) s
        = noise.E (fun p => (tr s (idx n s)).E (Vo n)
            - (tr s (act L (idx n s) p)).E (evalN tr r idx L noise n)) := by
      rw [WDist.E_sub, WDist.E_const, hM, hVs]; rfl
    rw [hsplit]
    calc noise.E (fun p => (tr s (idx n s)).E (Vo n)
            - (tr s (act L (idx n s) p)).E (evalN tr r idx L noise n))
        ≤ noise.E (fun p => (if anyFlip L p then Δ * W * ((M : Int) * W) ^ n else 0)
            + (W : Int) * Bd ((L * ew : Nat) : Int) ((M : Int) * W) Δ W n) :=
          WDist.E_mono _ _ _ hpt
      _ = (noise.wt (anyFlip L) : Int) * (Δ * W * ((M : Int) * W) ^ n)
            + (M : Int) * ((W : Int) * Bd ((L * ew : Nat) : Int) ((M : Int) * W) Δ W n) := by
          rw [WDist.E_add, WDist.E_ite, WDist.E_const, hM]
      _ ≤ _ := by
          have hub : (noise.wt (anyFlip L) : Int) ≤ ((L * ew : Nat) : Int) := by
            exact_mod_cast union_bound noise ew L hflip
          have hG : 0 ≤ Δ * (W : Int) * ((M : Int) * W) ^ n :=
            Int.mul_nonneg (Int.mul_nonneg hΔ (nn W))
              (pow_nn _ (Int.mul_nonneg (nn M) (nn W)) n)
          have h1 := Int.mul_le_mul_of_nonneg_right hub hG
          simp only [Bd]
          rw [← Int.mul_assoc (M : Int) (W : Int)]
          omega

theorem Bd_closed (Lew MW Δ W : Int) (hMW : 0 ≤ MW) :
    ∀ n : Nat, MW * Bd Lew MW Δ W n ≤ (n : Int) * (Lew * Δ * W) * MW ^ n := by
  intro n
  induction n with
  | zero => simp [Bd]
  | succ n ih =>
    have h := Int.mul_le_mul_of_nonneg_left ih hMW
    simp only [Bd]
    int_norm at h ⊢
    omega

/-- MAIN BOUND.  Dividing by (M·W)^(n+1) this reads:
    expected loss of the yes/no player  ≤  n · Δ · L · e      with e = ew / M. -/
theorem noisy_loss_bound {σ : Type} (tr : σ → Nat → WDist σ) (r : σ → Int) (idx : Nat → σ → Nat) (L : Nat)
    (noise : WDist (Nat → Bool)) (M W ew : Nat) (Δ : Int) (hΔ : 0 ≤ Δ) (Vo : Nat → σ → Int)
    (hM : noise.mass = M) (hflip : ∀ k, k < L → noise.wt (fun p => p k) ≤ ew)
    (hW : ∀ s a, (tr s a).mass = W) (hidx : ∀ n s, idx n s < 2 ^ L)
    (hV0 : ∀ s, Vo 0 s = r s)
    (hVs : ∀ n s, Vo (n + 1) s = (M : Int) * (tr s (idx n s)).E (Vo n))
    (hgap : ∀ n s a, (tr s (idx n s)).E (Vo n) - (tr s a).E (Vo n) ≤ Δ * W * ((M : Int) * W) ^ n) :
    ∀ n s, ((M : Int) * W) * (Vo n s - evalN tr r idx L noise n s)
      ≤ (n : Int) * (((L * ew : Nat) : Int) * Δ * W) * ((M : Int) * W) ^ n := by
  intro n s
  have hMW : 0 ≤ (M : Int) * W := Int.mul_nonneg (nn M) (nn W)
  have h1 := perf_diff tr r idx L noise M W ew Δ hΔ Vo hM hflip hW hidx hV0 hVs hgap n s
  have h2 := Int.mul_le_mul_of_nonneg_left h1 hMW
  exact Int.le_trans h2 (Bd_closed _ _ _ _ hMW n)

/-- THE PLAYER IS THE FAVOURITE: if the best response to the opponent is worth (in scaled units)
    more than the total error budget  n·Δ·L·e,  the yes/no player's expected result is positive.
    (In a colour-symmetric match the best response's value IS the opponent's exploitability.) -/
theorem favourite {σ : Type} (tr : σ → Nat → WDist σ) (r : σ → Int) (idx : Nat → σ → Nat) (L : Nat)
    (noise : WDist (Nat → Bool)) (M W ew : Nat) (Δ : Int) (hΔ : 0 ≤ Δ) (Vo : Nat → σ → Int)
    (hM : noise.mass = M) (hflip : ∀ k, k < L → noise.wt (fun p => p k) ≤ ew)
    (hW : ∀ s a, (tr s a).mass = W) (hidx : ∀ n s, idx n s < 2 ^ L)
    (hV0 : ∀ s, Vo 0 s = r s)
    (hVs : ∀ n s, Vo (n + 1) s = (M : Int) * (tr s (idx n s)).E (Vo n))
    (hgap : ∀ n s a, (tr s (idx n s)).E (Vo n) - (tr s a).E (Vo n) ≤ Δ * W * ((M : Int) * W) ^ n)
    (n : Nat) (s : σ)
    (hX : (n : Int) * (((L * ew : Nat) : Int) * Δ * W) * ((M : Int) * W) ^ n < ((M : Int) * W) * Vo n s) :
    0 < evalN tr r idx L noise n s := by
  have hb := noisy_loss_bound tr r idx L noise M W ew Δ hΔ Vo hM hflip hW hidx hV0 hVs hgap n s
  rw [Int.mul_sub] at hb
  have hpos : 0 < ((M : Int) * W) * evalN tr r idx L noise n s := by omega
  by_cases h : 0 < evalN tr r idx L noise n s
  · exact h
  · have h' : evalN tr r idx L noise n s ≤ 0 := by omega
    have := Int.mul_nonneg (nn (M * W)) (Int.neg_nonneg_of_nonpos h')
    simp only [Int.natCast_mul] at this
    rw [Int.mul_neg] at this
    omega

end YesNoLuck

/- sanity check of axioms (uncomment):
#print axioms YesNoLuck.favourite -/
