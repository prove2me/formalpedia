-- Prove2me | solution 1 for CommunicationComplexity.randomized_inner_product_retained_state_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T18:29:41.784504+00:00
-- url     : https://prove2.me/submissions/65293746-fae0-40e1-b3bb-ead4f149d313

import Mathlib

set_option autoImplicit false

namespace PvsNP.CausalRetainedState

open scoped BigOperators

abbrev BitBlock (m : ℕ) := Fin m → Bool

/-- A bit represented by its `+1` or `-1` sign. -/
def sign (b : Bool) : ℝ := if b then -1 else 1

private theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

private theorem sign_mul (a b : Bool) :
    sign a * sign b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> norm_num [sign]

/-- The sign of the Boolean inner product of two transcript blocks. -/
noncomputable def innerSign {m : ℕ} (x y : BitBlock m) : ℝ :=
  ∏ i, sign (x i && y i)

private theorem bit_row_orthogonality (a b : Bool) :
    (∑ y : Bool, sign (a && y) * sign (b && y)) = if a = b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [sign]

theorem innerSign_row_orthogonality {m : ℕ} (x z : BitBlock m) :
    (∑ y : BitBlock m, innerSign x y * innerSign z y) =
      if x = z then (2 : ℝ) ^ m else 0 := by
  classical
  simp only [innerSign, ← Finset.prod_mul_distrib]
  have split := Fintype.prod_sum (κ := fun _ : Fin m => Bool)
    (fun i y => sign (x i && y) * sign (z i && y))
  rw [← split]
  simp_rw [bit_row_orthogonality]
  by_cases equal : x = z
  · subst z
    simp
  · rw [if_neg equal]
    obtain ⟨i, different⟩ : ∃ i, x i ≠ z i := by
      by_contra! pointwise
      exact equal (funext pointwise)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg different)

/-- The unnormalized signed correlation between a retained-state reply and inner product. -/
noncomputable def correlation {m : ℕ} {State : Type} (retain : BitBlock m → State)
    (reply : State → BitBlock m → Bool) : ℝ :=
  ∑ x : BitBlock m, ∑ y : BitBlock m, sign (reply (retain x) y) * innerSign x y

private noncomputable def bucket {m : ℕ} {State : Type} [DecidableEq State]
    (retain : BitBlock m → State) (state : State) (y : BitBlock m) : ℝ :=
  ∑ x : BitBlock m, if retain x = state then innerSign x y else 0

private theorem bucket_square_sum {m : ℕ} {State : Type} [DecidableEq State]
    (retain : BitBlock m → State) (state : State) :
    (∑ y : BitBlock m, bucket retain state y ^ 2) =
      (2 : ℝ)^m * ∑ x : BitBlock m, if retain x = state then 1 else 0 := by
  classical
  let f (x : BitBlock m) : ℝ := if retain x = state then 1 else 0
  have factor (x y : BitBlock m) :
      (if retain x = state then innerSign x y else 0) = f x * innerSign x y := by
    dsimp only [f]
    split_ifs <;> simp
  have idempotent (x : BitBlock m) : f x * f x = f x := by
    dsimp only [f]
    split_ifs <;> simp
  unfold bucket
  simp_rw [factor, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  calc
    (∑ z : BitBlock m, ∑ y : BitBlock m,
        f x * innerSign x y * (f z * innerSign z y)) =
      ∑ z : BitBlock m, (f x * f z) * ∑ y : BitBlock m, innerSign x y * innerSign z y := by
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    _ = (2 : ℝ) ^ m * f x := by
      simp_rw [innerSign_row_orthogonality, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq]
      simp [idempotent, mul_comm]

/-- A reply determined by one of `card State` retained states has bounded squared
correlation, even with arbitrary computation on each side of the transcript split. -/
theorem correlation_sq_le {m : ℕ} {State : Type} [Fintype State]
    (retain : BitBlock m → State) (reply : State → BitBlock m → Bool) :
    correlation retain reply ^ 2 ≤ (Fintype.card State : ℝ) * ((2 : ℝ) ^ m) ^ 3 := by
  classical
  let A (p : State × BitBlock m) := sign (reply p.1 p.2)
  let B (p : State × BitBlock m) := bucket retain p.1 p.2
  have sumProduct : (∑ p, A p * B p) = correlation retain reply := by
    let term (state : State) (x y : BitBlock m) : ℝ :=
      if retain x = state then sign (reply state y) * innerSign x y else 0
    simp only [Fintype.sum_prod_type, A, B, bucket, Finset.mul_sum, mul_ite, mul_zero]
    unfold correlation
    change (∑ state : State, ∑ y : BitBlock m, ∑ x : BitBlock m, term state x y) = _
    calc
      _ = ∑ y : BitBlock m, ∑ state : State, ∑ x : BitBlock m, term state x y :=
        Finset.sum_comm
      _ = ∑ y : BitBlock m, ∑ x : BitBlock m, ∑ state : State, term state x y := by
        exact Finset.sum_congr rfl fun y _ => Finset.sum_comm
      _ = ∑ y : BitBlock m, ∑ x : BitBlock m, sign (reply (retain x) y) * innerSign x y := by
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro x _
        simp [term]
      _ = _ := Finset.sum_comm
  have sumFirst : (∑ p, A p ^ 2) = (Fintype.card State : ℝ) * (2 : ℝ) ^ m := by
    simp [A, sign_sq, Fintype.card_prod]
  have sumSecond : (∑ p, B p ^ 2) = ((2 : ℝ) ^ m) ^ 2 := by
    simp only [Fintype.sum_prod_type, B, bucket_square_sum, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [pow_two]
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ A B
  rw [sumProduct, sumFirst, sumSecond] at cauchy
  simpa [pow_succ, mul_assoc] using cauchy

/-- The parity of the number of coordinates where both challenge blocks have a 1. -/
def innerParity {m : ℕ} (x y : BitBlock m) : Bool :=
  decide (Odd (∑ i, (x i && y i).toNat))

private theorem sign_innerParity {m : ℕ} (x y : BitBlock m) :
    sign (innerParity x y) = innerSign x y := by
  have powSign (b : Bool) : sign b = (-1 : ℝ) ^ b.toNat := by
    cases b <;> norm_num [sign, Bool.toNat]
  calc
    _ = (-1 : ℝ) ^ (∑ i, (x i && y i).toNat) := by
      by_cases odd : Odd (∑ i, (x i && y i).toNat)
      · simp [innerParity, sign, odd, odd.neg_one_pow]
      · have even : Even (∑ i, (x i && y i).toNat) := Nat.not_odd_iff_even.mp odd
        simp [innerParity, sign, odd, even.neg_one_pow]
    _ = innerSign x y := by
      simp only [innerSign, powSign, Finset.prod_pow_eq_pow_sum]

/-- Average acceptance on independently uniform transcript blocks. -/
noncomputable def success {m : ℕ} {State : Type} (retain : BitBlock m → State)
    (reply : State → BitBlock m → Bool) : ℝ :=
  (∑ x : BitBlock m, ∑ y : BitBlock m,
    if reply (retain x) y = innerParity x y then 1 else 0) / ((2 : ℝ) ^ m) ^ 2

theorem correlation_eq_success {m : ℕ} {State : Type} (retain : BitBlock m → State)
    (reply : State → BitBlock m → Bool) :
    correlation retain reply = ((2 : ℝ) ^ m) ^ 2 * (2 * success retain reply - 1) := by
  have term (x y : BitBlock m) :
      sign (reply (retain x) y) * innerSign x y =
        2 * (if reply (retain x) y = innerParity x y then (1 : ℝ) else 0) - 1 := by
    rw [← sign_innerParity, sign_mul]
    split_ifs <;> norm_num
  unfold correlation success
  simp_rw [term, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_one]
  field_simp

/-- With uniform input and success at least two thirds, the retained state must
have at least `2^m / 9` possible values. -/
theorem two_thirds_requires_exponential_states {m : ℕ} {State : Type} [Fintype State]
    (retain : BitBlock m → State) (reply : State → BitBlock m → Bool)
    (good : (2 : ℝ) / 3 ≤ success retain reply) :
    2 ^ m ≤ 9 * Fintype.card State := by
  let N : ℝ := 2 ^ m
  have positive : 0 < N := by positivity
  have scaled : N ^ 2 ≤ 3 * correlation retain reply := by
    rw [correlation_eq_success]
    change N ^ 2 ≤ 3 * (N ^ 2 * (2 * success retain reply - 1))
    nlinarith [mul_nonneg (sq_nonneg N) (sub_nonneg.mpr good)]
  have squared : (N ^ 2) ^ 2 ≤ (3 * correlation retain reply) ^ 2 := by
    exact sq_le_sq' (by linarith [sq_nonneg N]) scaled
  have bound : N * N ^ 3 ≤ (9 * (Fintype.card State : ℝ)) * N ^ 3 := calc
    _ = (N ^ 2) ^ 2 := by ring
    _ ≤ (3 * correlation retain reply) ^ 2 := squared
    _ = 9 * correlation retain reply ^ 2 := by ring
    _ ≤ 9 * ((Fintype.card State : ℝ) * N ^ 3) := by
      exact mul_le_mul_of_nonneg_left (correlation_sq_le retain reply) (by norm_num)
    _ = _ := by ring
  have castBound : (2 : ℝ) ^ m ≤ 9 * (Fintype.card State : ℝ) :=
    le_of_mul_le_mul_right bound (pow_pos positive 3)
  exact_mod_cast castBound

/-- Fixing all random coins yields one retained-state strategy for each seed.
The lower bound also holds after averaging over any finite seed distribution
that is independent of the challenge blocks. -/
theorem randomized_two_thirds_requires_exponential_states {m : ℕ} {State Seed : Type}
    [Fintype State] [Fintype Seed]
    (retain : Seed → BitBlock m → State) (reply : Seed → State → BitBlock m → Bool)
    (weight : Seed → ℝ) (nonneg : ∀ seed, 0 ≤ weight seed) (total : (∑ seed, weight seed) = 1)
    (good : (2 : ℝ) / 3 ≤ ∑ seed, weight seed * success (retain seed) (reply seed)) :
    2 ^ m ≤ 9 * Fintype.card State := by
  classical
  by_contra narrow
  have small (seed : Seed) : success (retain seed) (reply seed) < (2 : ℝ) / 3 :=
    lt_of_not_ge fun accepted =>
      narrow (two_thirds_requires_exponential_states (retain seed) (reply seed) accepted)
  obtain ⟨seed, member, positive⟩ : ∃ seed ∈ Finset.univ, 0 < weight seed := by
    apply (Finset.sum_pos_iff_of_nonneg fun i _ => nonneg i).mp
    rw [total]
    norm_num
  have strict :
      (∑ s, weight s * success (retain s) (reply s)) < ∑ s, weight s * ((2 : ℝ) / 3) :=
    Finset.sum_lt_sum
      (fun s _ => mul_le_mul_of_nonneg_left (small s).le (nonneg s))
      ⟨seed, member, mul_lt_mul_of_pos_left (small seed) positive⟩
  rw [← Finset.sum_mul, total, one_mul] at strict
  exact (not_lt_of_ge good) strict

/-- A state represented by `k` bits can save at most three bits at success two thirds. -/
theorem two_thirds_requires_most_prefix_bits {m k : ℕ}
    (retain : BitBlock m → BitBlock k) (reply : BitBlock k → BitBlock m → Bool)
    (good : (2 : ℝ) / 3 ≤ success retain reply) : m ≤ k + 3 := by
  have bound := two_thirds_requires_exponential_states retain reply good
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] at bound
  by_contra! tooFewBits
  have power : (2 : ℕ) ^ (k + 4) ≤ 2 ^ m :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_add] at power
  norm_num at power
  have positive : 0 < (2 : ℕ) ^ k := by positivity
  omega

/-- Retaining the entire prefix and computing the inner product succeeds on every transcript. -/
theorem full_prefix_success (m : ℕ) :
    success (State := BitBlock m) id innerParity = 1 := by
  have nonzero : (2 : ℝ) ^ m ≠ 0 := by positivity
  simp [success, pow_two, nonzero]

end PvsNP.CausalRetainedState

open scoped BigOperators

theorem solution {m : ℕ} {State Seed : Type} [Fintype State] [Fintype Seed]
    (retain : Seed → (Fin m → Bool) → State)
    (reply : Seed → State → (Fin m → Bool) → Bool)
    (weight : Seed → ℝ) (nonneg : ∀ r, 0 ≤ weight r) (total : (∑ r, weight r) = 1)
    (good : (2 : ℝ) / 3 ≤ ∑ r, weight r *
      ((∑ x : Fin m → Bool, ∑ y : Fin m → Bool,
        if reply r (retain r x) y = decide (Odd (∑ i : Fin m, (x i && y i).toNat))
        then 1 else 0) / ((2 : ℝ) ^ m) ^ 2)) :
    2 ^ m ≤ 9 * Fintype.card State := by
  exact PvsNP.CausalRetainedState.randomized_two_thirds_requires_exponential_states
    retain reply weight nonneg total good

#print axioms solution
