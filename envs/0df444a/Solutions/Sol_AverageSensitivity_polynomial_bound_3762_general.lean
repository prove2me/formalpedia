-- Prove2me | solution 1 for AverageSensitivity.polynomial_bound_3762_general
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-16T12:54:34.266167+00:00
-- url     : https://prove2.me/submissions/0f539328-c783-4509-a78e-a86ac777468c

import Mathlib
import Definitions.Def_GotsmanLinial
import Theorems.Thm_AverageSensitivity_finite_coupling_refined
import Theorems.Thm_AverageSensitivity_extract_constant

namespace OAI.LeanBlast.GotsmanLinial
open scoped BigOperators
noncomputable def sensitiveEdgeCount {n : ℕ} (f : Cube n → ℝ) : ℕ :=
  ∑ i : Fin n, (sensitiveVertices f i).card
end OAI.LeanBlast.GotsmanLinial


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\Statement.lean

namespace OAI

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

@[simp] theorem flip_apply_same {n : ℕ} (i : Fin n) (x : Cube n) :
    flip i x i = !(x i) := by
  simp [flip]

theorem flip_apply_ne {n : ℕ} (i : Fin n) (x : Cube n) (j : Fin n) (h : j ≠ i) :
    flip i x j = x j := by
  simp [flip, h]

@[simp] theorem flip_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    flip i (flip i x) = x := by
  funext j
  by_cases h : j = i
  · subst j
    simp [flip]
  · simp [flip, h]

theorem flip_ne_self {n : ℕ} (i : Fin n) (x : Cube n) : flip i x ≠ x := by
  intro h
  have hi := congrFun h i
  cases hxi : x i <;> simp [flip, hxi] at hi

theorem flip_injective_direction {n : ℕ} (x : Cube n) :
    Function.Injective (fun i : Fin n => flip i x) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  cases hxi : x i <;> simp [flip, hij, hxi] at hi

theorem flip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flip i) :=
  flip_flip i

theorem flip_bijective {n : ℕ} (i : Fin n) : Function.Bijective (flip i) :=
  (flip_involutive i).bijective

@[simp] theorem cubeCoord_flip_same {n : ℕ} (x : Cube n) (i : Fin n) :
    cubeCoord (flip i x) i = -cubeCoord x i := by
  cases hxi : x i <;> simp [cubeCoord, flip, hxi]

theorem cubeCoord_flip_ne {n : ℕ} (x : Cube n) (i j : Fin n) (h : j ≠ i) :
    cubeCoord (flip i x) j = cubeCoord x j := by
  simp [cubeCoord, flip, h]

theorem cubeCoord_cases {n : ℕ} (x : Cube n) (i : Fin n) :
    cubeCoord x i = 1 ∨ cubeCoord x i = -1 := by
  cases hxi : x i <;> simp [cubeCoord, hxi]

@[simp] theorem cubeCoord_sq {n : ℕ} (x : Cube n) (i : Fin n) :
    (cubeCoord x i) ^ 2 = 1 := by
  cases hxi : x i <;> simp [cubeCoord, hxi]

@[simp] theorem thresholdSign_zero : thresholdSign 0 = 1 := by
  simp [thresholdSign]

theorem thresholdSign_eq_one_iff (t : ℝ) : thresholdSign t = 1 ↔ 0 ≤ t := by
  by_cases h : 0 ≤ t
  · simp [thresholdSign, h]
  · simp [thresholdSign, h, show (-1 : ℝ) ≠ 1 by norm_num]

theorem thresholdSign_eq_neg_one_iff (t : ℝ) : thresholdSign t = -1 ↔ t < 0 := by
  by_cases h : 0 ≤ t
  · simp [thresholdSign, h, not_lt.mpr h, show (1 : ℝ) ≠ -1 by norm_num]
  · simp [thresholdSign, h, lt_of_not_ge h]

theorem thresholdSign_cases (t : ℝ) : thresholdSign t = 1 ∨ thresholdSign t = -1 := by
  unfold thresholdSign
  split <;> simp

@[simp] theorem thresholdSign_sq (t : ℝ) : thresholdSign t ^ 2 = 1 := by
  rcases thresholdSign_cases t with h | h <;> simp [h]

@[simp] theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]

/-- The Boolean encoding represents every sign vector exactly once. -/
noncomputable def cubeEquivSignVectors (n : ℕ) :
    Cube n ≃ {x : Fin n → ℝ // ∀ i, x i = 1 ∨ x i = -1} := by
  classical
  exact
    { toFun := fun x => ⟨cubeCoord x, cubeCoord_cases x⟩
      invFun := fun x i => decide (x.1 i = 1)
      left_inv := by
        intro x
        funext i
        cases hxi : x i <;> simp [cubeCoord, hxi, show (-1 : ℝ) ≠ 1 by norm_num]
      right_inv := by
        intro x
        apply Subtype.ext
        funext i
        rcases x.2 i with hxi | hxi <;>
          simp [cubeCoord, hxi, show (-1 : ℝ) ≠ 1 by norm_num] }

theorem averageSensitivity_eq_count {n : ℕ} (f : Cube n → ℝ) :
    averageSensitivity f = (sensitiveEdgeCount f : ℝ) / (2 : ℝ) ^ n := by
  simp [averageSensitivity, sensitiveEdgeCount, Finset.sum_div]

theorem averageSensitivity_eq_uniform {n : ℕ} (f : Cube n → ℝ) :
    averageSensitivity f =
      ∑ i : Fin n, ((sensitiveVertices f i).card : ℝ) / (Fintype.card (Cube n) : ℝ) := by
  simp [averageSensitivity]

end LeanBlast.GotsmanLinial

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\BinomialMoments.lean

namespace OAI

/-!
Exact finite moments of the symmetric binomial weights. These identities provide
the grading multiplicities and the variance used in the finite coupling estimate.
No probabilistic assumptions or measures enter the statements.
-/

namespace LeanBlast.GotsmanLinial

open scoped BigOperators

/-- The normalizing denominator is positive, also when `n = 0`. -/
theorem binomialDenominator_pos (n : ℕ) : 0 < (2 : ℝ) ^ n :=
  pow_pos (by norm_num) n

theorem binomialDenominator_ne_zero (n : ℕ) : (2 : ℝ) ^ n ≠ 0 :=
  ne_of_gt (binomialDenominator_pos n)

/-- The real sum of one row of Pascal's triangle. -/
theorem sum_choose_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)) = (2 : ℝ) ^ n := by
  exact_mod_cast Nat.sum_range_choose n

/-- Pascal recursion for an arbitrary real function of the binomial index. -/
theorem sum_choose_succ (n : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℝ) * f k) =
      (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * f k) +
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * f (k + 1) :=
  Finset.sum_choose_succ_mul (fun k _ => f k) n

/-- The first raw binomial moment, with a formula valid at `n = 0`. -/
theorem sum_choose_mul_index_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ)) =
      (n : ℝ) * (2 : ℝ) ^ n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_choose_succ]
      simp_rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      rw [Finset.sum_add_distrib, ih, sum_choose_range]
      simp only [pow_succ]
      ring

/-- The second raw binomial moment, with a formula valid at `n = 0`. -/
theorem sum_choose_mul_index_sq_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 : ℝ) ^ n / 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_choose_succ]
      have hshift :
          (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) =
            (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ) ^ 2) +
              2 * (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ)) +
              ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        push_cast
        ring
      rw [hshift, ih, sum_choose_mul_index_range, sum_choose_range]
      simp only [pow_succ, Nat.cast_add, Nat.cast_one]
      ring

/-- Exact centered second moment before dividing by `2^n`. -/
theorem sum_choose_centered_sq_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2) =
      (n : ℝ) * (2 : ℝ) ^ n / 4 := by
  calc
    _ = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ) ^ 2) -
          (n : ℝ) * (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ)) +
          ((n : ℝ) ^ 2 / 4) * (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = _ := by
        rw [sum_choose_mul_index_sq_range, sum_choose_mul_index_range, sum_choose_range]
        ring

/-- The same total mass on the grading-index type. -/
theorem sum_choose (n : ℕ) :
    (∑ k : Fin (n + 1), (n.choose k.val : ℝ)) = (2 : ℝ) ^ n := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (n.choose k : ℝ))]
  exact sum_choose_range n

theorem sum_choose_mul_index (n : ℕ) :
    (∑ k : Fin (n + 1), (n.choose k.val : ℝ) * (k.val : ℝ)) =
      (n : ℝ) * (2 : ℝ) ^ n / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (n.choose k : ℝ) * (k : ℝ))]
  exact sum_choose_mul_index_range n

theorem sum_choose_mul_index_sq (n : ℕ) :
    (∑ k : Fin (n + 1), (n.choose k.val : ℝ) * (k.val : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 : ℝ) ^ n / 4 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (n.choose k : ℝ) * (k : ℝ) ^ 2)]
  exact sum_choose_mul_index_sq_range n

theorem sum_choose_centered_sq (n : ℕ) :
    (∑ k : Fin (n + 1),
      (n.choose k.val : ℝ) * ((k.val : ℝ) - (n : ℝ) / 2) ^ 2) =
      (n : ℝ) * (2 : ℝ) ^ n / 4 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (n.choose k : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2)]
  exact sum_choose_centered_sq_range n

/-- The symmetric binomial probability weights, presented as a finite real function. -/
noncomputable def binomialWeight (n : ℕ) (k : Fin (n + 1)) : ℝ :=
  (n.choose k.val : ℝ) / (2 : ℝ) ^ n

theorem binomialWeight_nonneg (n : ℕ) (k : Fin (n + 1)) :
    0 ≤ binomialWeight n k :=
  div_nonneg (Nat.cast_nonneg _) (le_of_lt (binomialDenominator_pos n))

theorem sum_binomialWeight (n : ℕ) : (∑ k : Fin (n + 1), binomialWeight n k) = 1 := by
  unfold binomialWeight
  rw [← Finset.sum_div, sum_choose, div_self (binomialDenominator_ne_zero n)]

theorem binomialWeight_mean (n : ℕ) :
    (∑ k : Fin (n + 1), binomialWeight n k * (k.val : ℝ)) = (n : ℝ) / 2 := by
  unfold binomialWeight
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, sum_choose_mul_index]
  field_simp [binomialDenominator_ne_zero n]

theorem binomialWeight_variance (n : ℕ) :
    (∑ k : Fin (n + 1), binomialWeight n k * ((k.val : ℝ) - (n : ℝ) / 2) ^ 2) =
      (n : ℝ) / 4 := by
  unfold binomialWeight
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, sum_choose_centered_sq]
  field_simp [binomialDenominator_ne_zero n]

/-- The binomial coefficients are invariant under reflection about `n/2`. -/
theorem choose_reflect (n : ℕ) (k : Fin (n + 1)) :
    n.choose (n - k.val) = n.choose k.val :=
  Nat.choose_symm (Nat.le_of_lt_succ k.isLt)

theorem choose_rev (n : ℕ) (k : Fin (n + 1)) :
    n.choose k.rev.val = n.choose k.val := by
  simpa only [Fin.val_rev, Nat.add_sub_add_right] using choose_reflect n k

theorem binomialWeight_rev (n : ℕ) (k : Fin (n + 1)) :
    binomialWeight n k.rev = binomialWeight n k := by
  simp only [binomialWeight, choose_rev]

theorem index_rev_real (n : ℕ) (k : Fin (n + 1)) :
    (k.rev.val : ℝ) = (n : ℝ) - (k.val : ℝ) := by
  rw [Fin.val_rev, Nat.add_sub_add_right, Nat.cast_sub (Nat.le_of_lt_succ k.isLt)]

/-- Reflecting a binomial index preserves every real finite expectation. -/
theorem binomialWeight_reflect (n : ℕ) (φ : ℝ → ℝ) :
    (∑ k : Fin (n + 1), binomialWeight n k * φ ((n : ℝ) - (k.val : ℝ))) =
      ∑ k : Fin (n + 1), binomialWeight n k * φ (k.val : ℝ) := by
  have h := Equiv.sum_comp (Fin.revPerm (n := n + 1))
    (fun k : Fin (n + 1) => binomialWeight n k * φ (k.val : ℝ))
  change (∑ k : Fin (n + 1), binomialWeight n k.rev * φ (k.rev.val : ℝ)) = _ at h
  simpa only [binomialWeight_rev, index_rev_real] using h

/-- Standard deviation corresponding to the preceding finite variance identity. -/
theorem binomialSigma_sq (n : ℕ) : (Real.sqrt (n : ℝ) / 2) ^ 2 = (n : ℝ) / 4 := by
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  norm_num

theorem binomialSigma_nonneg (n : ℕ) : 0 ≤ Real.sqrt (n : ℝ) / 2 :=
  div_nonneg (Real.sqrt_nonneg _) (by norm_num)

end LeanBlast.GotsmanLinial

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\ScalarIncrements.lean

namespace OAI

/-!
# Scalar inequalities for the one-sided coupling estimate

The increasing function `couplingPotential m t = (t-m)|t-m|/2` controls
squared distances from below and has a trapezoidal increment bound from above.
All arguments here are algebraic, by splitting according to the positions of
the endpoints relative to the center `m`.
-/

namespace LeanBlast.GotsmanLinial

/-- The scalar potential used in the one-sided coupling argument. -/
noncomputable def couplingPotential (m t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (t - m) * |t - m|

@[simp] theorem couplingPotential_self (m : ℝ) : couplingPotential m m = 0 := by
  simp [couplingPotential]

/-- Both increment inequalities hold even when the endpoints coincide. -/
theorem couplingPotential_increment_bounds (m : ℝ) {u v : ℝ} (huv : u ≤ v) :
    (v - u) ^ 2 / 4 ≤ couplingPotential m v - couplingPotential m u ∧
      couplingPotential m v - couplingPotential m u ≤
        (v - u) / 2 * (|u - m| + |v - m|) := by
  by_cases hum : u ≤ m
  · by_cases hvm : v ≤ m
    · simp only [couplingPotential, abs_of_nonpos (sub_nonpos.mpr hum),
        abs_of_nonpos (sub_nonpos.mpr hvm)]
      constructor
      · nlinarith [sq_nonneg (v - u),
          mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hvm)]
      · nlinarith
    · have hmv : m ≤ v := (not_le.mp hvm).le
      simp only [couplingPotential, abs_of_nonpos (sub_nonpos.mpr hum),
        abs_of_nonneg (sub_nonneg.mpr hmv)]
      constructor
      · nlinarith [sq_nonneg (u + v - 2 * m)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hum) (sub_nonneg.mpr hmv)]
  · have hmu : m ≤ u := (not_le.mp hum).le
    have hmv : m ≤ v := hmu.trans huv
    simp only [couplingPotential, abs_of_nonneg (sub_nonneg.mpr hmu),
      abs_of_nonneg (sub_nonneg.mpr hmv)]
    constructor
    · nlinarith [sq_nonneg (v - u),
        mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hmu)]
    · nlinarith

theorem couplingPotential_increment_lower (m : ℝ) {u v : ℝ} (huv : u ≤ v) :
    (v - u) ^ 2 / 4 ≤ couplingPotential m v - couplingPotential m u :=
  (couplingPotential_increment_bounds m huv).1

theorem couplingPotential_increment_upper (m : ℝ) {u v : ℝ} (huv : u ≤ v) :
    couplingPotential m v - couplingPotential m u ≤
      (v - u) / 2 * (|u - m| + |v - m|) :=
  (couplingPotential_increment_bounds m huv).2

theorem monotone_couplingPotential (m : ℝ) : Monotone (couplingPotential m) := by
  intro u v huv
  have h := couplingPotential_increment_lower m huv
  nlinarith [sq_nonneg (v - u)]

theorem strictMono_couplingPotential (m : ℝ) : StrictMono (couplingPotential m) := by
  intro u v huv
  have h := couplingPotential_increment_lower m huv.le
  have hs := mul_pos (sub_pos.mpr huv) (sub_pos.mpr huv)
  nlinarith

@[simp] theorem couplingPotential_le_iff (m u v : ℝ) :
    couplingPotential m u ≤ couplingPotential m v ↔ u ≤ v :=
  (strictMono_couplingPotential m).le_iff_le

@[simp] theorem couplingPotential_lt_iff (m u v : ℝ) :
    couplingPotential m u < couplingPotential m v ↔ u < v :=
  (strictMono_couplingPotential m).lt_iff_lt

@[simp] theorem couplingPotential_eq_iff (m u v : ℝ) :
    couplingPotential m u = couplingPotential m v ↔ u = v :=
  (strictMono_couplingPotential m).injective.eq_iff

theorem couplingPotential_sub_nonneg_iff (m u v : ℝ) :
    0 ≤ couplingPotential m v - couplingPotential m u ↔ u ≤ v := by
  rw [sub_nonneg, couplingPotential_le_iff]

theorem couplingPotential_sub_pos_iff (m u v : ℝ) :
    0 < couplingPotential m v - couplingPotential m u ↔ u < v := by
  rw [sub_pos, couplingPotential_lt_iff]

theorem abs_couplingPotential_sub_of_le (m : ℝ) {u v : ℝ} (huv : u ≤ v) :
    |couplingPotential m v - couplingPotential m u| =
      couplingPotential m v - couplingPotential m u :=
  abs_of_nonneg ((couplingPotential_sub_nonneg_iff m u v).mpr huv)

/-- The pointwise lower bound in the coupling argument, without ordering the
two real variables. -/
theorem sq_sub_le_four_mul_abs_potential_sub (m u v : ℝ) :
    (u - v) ^ 2 ≤ 4 * |couplingPotential m u - couplingPotential m v| := by
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm, abs_couplingPotential_sub_of_le m huv]
    have h := couplingPotential_increment_lower m huv
    nlinarith
  · rw [abs_couplingPotential_sub_of_le m hvu]
    have h := couplingPotential_increment_lower m hvu
    nlinarith

/-- An upper bound for the positive part of a potential increment under a
one-sided bound on the original increment. -/
theorem max_couplingPotential_increment_le (m a u v : ℝ)
    (ha : 0 ≤ a) (hstep : v - u ≤ a) :
    max (couplingPotential m v - couplingPotential m u) 0 ≤
      a / 2 * (|u - m| + |v - m|) := by
  have hs : 0 ≤ |u - m| + |v - m| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  by_cases huv : u ≤ v
  · rw [max_eq_left ((couplingPotential_sub_nonneg_iff m u v).mpr huv)]
    have h := couplingPotential_increment_upper m huv
    have hp := mul_nonneg (sub_nonneg.mpr hstep) hs
    nlinarith
  · have hvu : v ≤ u := (not_le.mp huv).le
    rw [max_eq_right (sub_nonpos.mpr ((monotone_couplingPotential m) hvu))]
    nlinarith [mul_nonneg ha hs]

end LeanBlast.GotsmanLinial

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\FiniteCoupling.lean

namespace OAI

/-!
# A finite one-sided coupling estimate

This is a finite weighted probabilistic estimate. Equal
marginals are expressed as equality of the weighted expectations of every
real function. The increment bound is required only on the support of the
nonnegative probability weights.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

variable {Ω : Type*} [Fintype Ω]

/-- Weighted Cauchy--Schwarz bounds the first absolute moment by a bound on
the second moment. Zero weights are allowed. -/
theorem weighted_abs_le_of_second_moment (w f : Ω → ℝ) (σ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hσ : 0 ≤ σ)
    (hsecond : ∑ i, w i * (f i) ^ 2 ≤ σ ^ 2) :
    ∑ i, w i * |f i| ≤ σ := by
  have hcs : (∑ i, w i * |f i|) ^ 2 ≤
      (∑ i, w i) * ∑ i, w i * (f i) ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i _
      exact hw i
    · intro i _
      exact mul_nonneg (hw i) (sq_nonneg (f i))
    · intro i _
      apply le_of_eq
      rw [mul_pow, sq_abs]
      ring
  rw [hprob, one_mul] at hcs
  have hnonneg : 0 ≤ ∑ i, w i * |f i| :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (abs_nonneg (f i)))
  nlinarith

/-- A weighted mean-zero variable has absolute first moment twice the first
moment of its positive part. This identity does not need positivity of the weights. -/
theorem weighted_abs_eq_twice_positive_part (w z : Ω → ℝ)
    (hzero : ∑ i, w i * z i = 0) :
    ∑ i, w i * |z i| = 2 * ∑ i, w i * max (z i) 0 := by
  calc
    ∑ i, w i * |z i| =
        (∑ i, w i * |z i|) + ∑ i, w i * z i := by rw [hzero, add_zero]
    _ = ∑ i, (w i * |z i| + w i * z i) := by rw [Finset.sum_add_distrib]
    _ = ∑ i, 2 * (w i * max (z i) 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : 0 ≤ z i
      · rw [abs_of_nonneg hi, max_eq_left hi]
        ring
      · have hi' : z i ≤ 0 := (lt_of_not_ge hi).le
        rw [abs_of_nonpos hi', max_eq_right hi']
        ring
    _ = 2 * ∑ i, w i * max (z i) 0 := by rw [Finset.mul_sum]

/-- The finite one-sided coupling lemma: identical marginals and an upper
bound `a` on `V - U` bound the mean square displacement by `8 * a * σ`.

The center `m` may be arbitrary. Taking it to be the common mean recovers the
variance bound with variance `σ²`; only the displayed second moment is used. -/
theorem finite_one_sided_coupling_bound (w U V : Ω → ℝ) (m σ a : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hsame : ∀ φ : ℝ → ℝ, ∑ i, w i * φ (U i) = ∑ i, w i * φ (V i))
    (hσ : 0 ≤ σ) (ha : 0 ≤ a)
    (hvariance : ∑ i, w i * (U i - m) ^ 2 = σ ^ 2)
    (hstep : ∀ i, w i ≠ 0 → V i - U i ≤ a) :
    ∑ i, w i * (U i - V i) ^ 2 ≤ 8 * a * σ := by
  let z : Ω → ℝ := fun i => couplingPotential m (V i) - couplingPotential m (U i)
  have hz : ∑ i, w i * z i = 0 := by
    simp only [z, mul_sub, Finset.sum_sub_distrib]
    rw [hsame (couplingPotential m), sub_self]
  have habs := weighted_abs_eq_twice_positive_part w z hz
  have hU : ∑ i, w i * |U i - m| ≤ σ :=
    weighted_abs_le_of_second_moment w (fun i => U i - m) σ hw hprob hσ hvariance.le
  have hV : ∑ i, w i * |V i - m| ≤ σ := by
    rw [← hsame (fun t => |t - m|)]
    exact hU
  have hpositive : ∑ i, w i * max (z i) 0 ≤ a * σ := by
    calc
      ∑ i, w i * max (z i) 0 ≤
          ∑ i, w i * (a / 2 * (|U i - m| + |V i - m|)) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : w i = 0
        · simp only [hi, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left
            (max_couplingPotential_increment_le m a (U i) (V i) ha (hstep i hi))
            (hw i)
      _ = a / 2 * ((∑ i, w i * |U i - m|) + ∑ i, w i * |V i - m|) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ a / 2 * (σ + σ) :=
        mul_le_mul_of_nonneg_left (add_le_add hU hV) (div_nonneg ha (by norm_num))
      _ = a * σ := by ring
  have hsquare : ∑ i, w i * (U i - V i) ^ 2 ≤ 4 * ∑ i, w i * |z i| := by
    calc
      ∑ i, w i * (U i - V i) ^ 2 ≤ ∑ i, w i * (4 * |z i|) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hw i)
        dsimp only [z]
        rw [abs_sub_comm]
        exact sq_sub_le_four_mul_abs_potential_sub m (U i) (V i)
      _ = 4 * ∑ i, w i * |z i| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  calc
    ∑ i, w i * (U i - V i) ^ 2 ≤ 4 * ∑ i, w i * |z i| := hsquare
    _ = 8 * ∑ i, w i * max (z i) 0 := by rw [habs]; ring
    _ ≤ 8 * (a * σ) := mul_le_mul_of_nonneg_left hpositive (by norm_num)
    _ = 8 * a * σ := by ring

end LeanBlast.GotsmanLinial

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\HilbertSchmidt.lean

namespace OAI

open scoped BigOperators ComplexConjugate

namespace LeanBlast.GotsmanLinial

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Hilbert--Schmidt norm squared for the counting inner product.
This explicit entry sum does not use any norm instance on matrices. -/
noncomputable def hsNormSq (A : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem hsNormSq_nonneg (A : Matrix ι κ ℂ) : 0 ≤ hsNormSq A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

@[simp] theorem hsNormSq_zero : hsNormSq (0 : Matrix ι κ ℂ) = 0 := by
  simp [hsNormSq]

theorem hsNormSq_smul (c : ℂ) (A : Matrix ι κ ℂ) :
    hsNormSq (c • A) = ‖c‖ ^ 2 * hsNormSq A := by
  simp [hsNormSq, mul_pow, Finset.mul_sum]

theorem hsNormSq_real_smul (c : ℝ) (A : Matrix ι κ ℂ) :
    hsNormSq ((c : ℂ) • A) = c ^ 2 * hsNormSq A := by
  rw [hsNormSq_smul]
  simp

@[simp] theorem hsNormSq_conjTranspose (A : Matrix ι κ ℂ) :
    hsNormSq A.conjTranspose = hsNormSq A := by
  simp only [hsNormSq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

theorem ofReal_sq_norm (z : ℂ) : (↑(‖z‖ ^ 2) : ℂ) = star z * z := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, Complex.star_def]

private theorem ofReal_fintype_sum (f : ι → ℝ) :
    (↑(∑ i, f i) : ℂ) = ∑ i, (f i : ℂ) :=
  map_sum Complex.ofRealHom f Finset.univ

omit [Fintype κ] in
theorem ofReal_sum_sq_norm_column (A : Matrix ι κ ℂ) (j : κ) :
    (↑(∑ i, ‖A i j‖ ^ 2) : ℂ) = (A.conjTranspose * A) j j := by
  rw [ofReal_fintype_sum]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_congr rfl fun i _ => ofReal_sq_norm _

theorem ofReal_hsNormSq (A : Matrix ι κ ℂ) :
    (hsNormSq A : ℂ) = Matrix.trace (A.conjTranspose * A) := by
  rw [hsNormSq, Finset.sum_comm]
  rw [ofReal_fintype_sum]
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_congr rfl fun j _ => ofReal_sum_sq_norm_column A j

theorem hsNormSq_eq_re_trace (A : Matrix ι κ ℂ) :
    hsNormSq A = (Matrix.trace (A.conjTranspose * A)).re := by
  exact congrArg Complex.re (ofReal_hsNormSq A)

theorem hsNormSq_eq_sum_columns (A : Matrix ι κ ℂ) :
    hsNormSq A = ∑ j, ∑ i, ‖A i j‖ ^ 2 := by
  exact Finset.sum_comm

omit [Fintype κ] in
theorem sum_sq_norm_column_eq_re (A : Matrix ι κ ℂ) (j : κ) :
    ∑ i, ‖A i j‖ ^ 2 = ((A.conjTranspose * A) j j).re := by
  exact congrArg Complex.re (ofReal_sum_sq_norm_column A j)

theorem hsNormSq_mul_left_of_unitary [DecidableEq ι]
    (U : Matrix ι ι ℂ) (A : Matrix ι κ ℂ) (hU : U.conjTranspose * U = 1) :
    hsNormSq (U * A) = hsNormSq A := by
  rw [hsNormSq_eq_re_trace, hsNormSq_eq_re_trace]
  congr 2
  calc
    (U * A).conjTranspose * (U * A) = A.conjTranspose *
        (U.conjTranspose * U) * A := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = A.conjTranspose * A := by rw [hU, Matrix.mul_one]

theorem hsNormSq_mul_right_of_unitary [DecidableEq κ]
    (A : Matrix ι κ ℂ) (U : Matrix κ κ ℂ) (hU : U * U.conjTranspose = 1) :
    hsNormSq (A * U) = hsNormSq A := by
  rw [← hsNormSq_conjTranspose (A * U), Matrix.conjTranspose_mul]
  rw [hsNormSq_mul_left_of_unitary U.conjTranspose A.conjTranspose]
  · exact hsNormSq_conjTranspose A
  · simpa using hU

@[simp] theorem hsNormSq_diagonal [DecidableEq ι] (d : ι → ℂ) :
    hsNormSq (Matrix.diagonal d) = ∑ i, ‖d i‖ ^ 2 := by
  simp [hsNormSq, Matrix.diagonal_apply, apply_ite]

@[simp] theorem hsNormSq_one [DecidableEq ι] :
    hsNormSq (1 : Matrix ι ι ℂ) = Fintype.card ι := by
  rw [hsNormSq_eq_re_trace]
  simp

theorem hsNormSq_of_unitary [DecidableEq ι] (U : Matrix ι ι ℂ)
    (hU : U.conjTranspose * U = 1) : hsNormSq U = Fintype.card ι := by
  rw [hsNormSq_eq_re_trace, hU]
  simp

theorem hsNormSq_diagonal_of_norm_one [DecidableEq ι] (d : ι → ℂ)
    (hd : ∀ i, ‖d i‖ = 1) :
    hsNormSq (Matrix.diagonal d) = Fintype.card ι := by
  simp [hsNormSq_diagonal, hd]

theorem hsNormSq_projection (P : Matrix ι ι ℂ)
    (hself : P.conjTranspose = P) (hidem : P * P = P) :
    hsNormSq P = (Matrix.trace P).re := by
  rw [hsNormSq_eq_re_trace, hself, hidem]

theorem sum_sq_norm_column_of_unitary [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U.conjTranspose * U = 1) (j : ι) :
    ∑ i, ‖U i j‖ ^ 2 = 1 := by
  rw [sum_sq_norm_column_eq_re, hU]
  simp

theorem sq_norm_entry_le_one_of_unitary [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U.conjTranspose * U = 1) (i j : ι) :
    ‖U i j‖ ^ 2 ≤ 1 := by
  rw [← sum_sq_norm_column_of_unitary U hU j]
  exact Finset.single_le_sum (fun k _ => sq_nonneg ‖U k j‖) (Finset.mem_univ i)

end LeanBlast.GotsmanLinial

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\ProjectionBlocks.lean

namespace OAI

/-!
# Matrix blocks of a finite orthogonal projection family

The Hilbert--Schmidt quantity below is the explicit sum of squared entry norms
rather than an ambient matrix norm instance.
-/

open scoped BigOperators ComplexConjugate
open Module

noncomputable section

namespace LeanBlast.GotsmanLinial

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- A finite orthogonal decomposition of the identity by Hermitian projections. -/
structure OrthogonalProjectionFamily (P : κ → Matrix ι ι ℂ) : Prop where
  selfAdjoint : ∀ k, IsSelfAdjoint (P k)
  idempotent : ∀ k, P k * P k = P k
  orthogonal : ∀ r s, r ≠ s → P r * P s = 0
  sum_eq_one : ∑ k, P k = 1

namespace OrthogonalProjectionFamily

variable {P : κ → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)

include hP

theorem conjTranspose_eq (k : κ) : (P k).conjTranspose = P k := by
  simpa only [IsSelfAdjoint, Matrix.star_eq_conjTranspose] using hP.selfAdjoint k

theorem mul_eq_ite [DecidableEq κ] (r s : κ) :
    P r * P s = if r = s then P r else 0 := by
  by_cases hrs : r = s
  · subst s
    simp [hP.idempotent]
  · simp [hrs, hP.orthogonal r s hrs]

end OrthogonalProjectionFamily

variable {P : κ → Matrix ι ι ℂ}

theorem sum_projection_blocks (hP : OrthogonalProjectionFamily P) (B : Matrix ι ι ℂ) :
    (∑ r, ∑ s, P s * B * P r) = B := by
  simp_rw [← Matrix.sum_mul, hP.sum_eq_one, Matrix.one_mul]
  rw [← Matrix.mul_sum, hP.sum_eq_one, Matrix.mul_one]

theorem projection_block_ext (hP : OrthogonalProjectionFamily P)
    {A B : Matrix ι ι ℂ} (h : ∀ r s, P s * A * P r = P s * B * P r) : A = B := by
  rw [← sum_projection_blocks hP A, ← sum_projection_blocks hP B]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => h r s

/-- The real-valued spectral multiplier defined by the projection family. -/
def matrixGrading (P : κ → Matrix ι ι ℂ) (weight : κ → ℝ) : Matrix ι ι ℂ :=
  ∑ k, (weight k : ℂ) • P k

theorem projection_mul_matrixGrading (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (s : κ) : P s * matrixGrading P weight = (weight s : ℂ) • P s := by
  classical
  simp only [matrixGrading, Matrix.mul_sum, Matrix.mul_smul, hP.mul_eq_ite]
  simp

theorem matrixGrading_mul_projection (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (r : κ) : matrixGrading P weight * P r = (weight r : ℂ) • P r := by
  classical
  simp only [matrixGrading, Matrix.sum_mul, Matrix.smul_mul, hP.mul_eq_ite]
  simp

theorem projection_commutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) (r s : κ) :
    P s * (matrixGrading P weight * B - B * matrixGrading P weight) * P r =
      ((weight s - weight r : ℝ) : ℂ) • (P s * B * P r) := by
  rw [Matrix.mul_sub, Matrix.sub_mul]
  calc
    P s * (matrixGrading P weight * B) * P r -
        P s * (B * matrixGrading P weight) * P r =
      (P s * matrixGrading P weight) * B * P r -
        P s * B * (matrixGrading P weight * P r) := by simp only [Matrix.mul_assoc]
    _ = ((weight s : ℂ) • P s) * B * P r -
        P s * B * ((weight r : ℂ) • P r) := by
      rw [projection_mul_matrixGrading hP, matrixGrading_mul_projection hP]
    _ = ((weight s - weight r : ℝ) : ℂ) • (P s * B * P r) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Complex.ofReal_sub, sub_smul]

theorem projection_anticommutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) (r s : κ) :
    P s * (matrixGrading P weight * B + B * matrixGrading P weight) * P r =
      ((weight s + weight r : ℝ) : ℂ) • (P s * B * P r) := by
  rw [Matrix.mul_add, Matrix.add_mul]
  calc
    P s * (matrixGrading P weight * B) * P r +
        P s * (B * matrixGrading P weight) * P r =
      (P s * matrixGrading P weight) * B * P r +
        P s * B * (matrixGrading P weight * P r) := by simp only [Matrix.mul_assoc]
    _ = ((weight s : ℂ) • P s) * B * P r +
        P s * B * ((weight r : ℂ) • P r) := by
      rw [projection_mul_matrixGrading hP, matrixGrading_mul_projection hP]
    _ = ((weight s + weight r : ℝ) : ℂ) • (P s * B * P r) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Complex.ofReal_add, add_smul]

omit [DecidableEq ι] in
theorem trace_projection_sandwich (Q A : Matrix ι ι ℂ) (hQ : Q * Q = Q) :
    Matrix.trace (Q * A * Q) = Matrix.trace (Q * A) := by
  rw [Matrix.trace_mul_cycle, hQ]

theorem hsNormSq_projection_mul (hP : OrthogonalProjectionFamily P)
    (s : κ) (B : Matrix ι ι ℂ) :
    hsNormSq (P s * B) = (Matrix.trace (B.conjTranspose * P s * B)).re := by
  rw [hsNormSq_eq_re_trace, Matrix.conjTranspose_mul, hP.conjTranspose_eq]
  congr 2
  calc
    (B.conjTranspose * P s) * (P s * B) =
        B.conjTranspose * (P s * P s) * B := by simp only [Matrix.mul_assoc]
    _ = B.conjTranspose * P s * B := by rw [hP.idempotent]

theorem hsNormSq_mul_projection (hP : OrthogonalProjectionFamily P)
    (r : κ) (B : Matrix ι ι ℂ) :
    hsNormSq (B * P r) = (Matrix.trace (P r * (B.conjTranspose * B))).re := by
  rw [hsNormSq_eq_re_trace, Matrix.conjTranspose_mul, hP.conjTranspose_eq]
  have heq : (P r * B.conjTranspose) * (B * P r) =
      P r * (B.conjTranspose * B) * P r := by simp only [Matrix.mul_assoc]
  rw [heq, trace_projection_sandwich _ _ (hP.idempotent r)]

theorem hsNormSq_left_projection_decomposition (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) : hsNormSq B = ∑ s, hsNormSq (P s * B) := by
  simp_rw [hsNormSq_projection_mul hP]
  rw [← Complex.re_sum, ← Matrix.trace_sum]
  simp_rw [← Matrix.sum_mul]
  rw [← Matrix.mul_sum, hP.sum_eq_one, Matrix.mul_one, hsNormSq_eq_re_trace]

theorem hsNormSq_right_projection_decomposition (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) : hsNormSq B = ∑ r, hsNormSq (B * P r) := by
  simp_rw [hsNormSq_mul_projection hP]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul,
    hP.sum_eq_one, Matrix.one_mul, hsNormSq_eq_re_trace]

theorem hsNormSq_block_parseval (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) :
    hsNormSq B = ∑ r, ∑ s, hsNormSq (P s * B * P r) := by
  rw [hsNormSq_right_projection_decomposition hP B]
  apply Finset.sum_congr rfl
  intro r _
  simpa only [Matrix.mul_assoc] using hsNormSq_left_projection_decomposition hP (B * P r)

theorem hsNormSq_matrixGrading (hP : OrthogonalProjectionFamily P) (weight : κ → ℝ) :
    hsNormSq (matrixGrading P weight) = ∑ r, weight r ^ 2 * hsNormSq (P r) := by
  classical
  rw [hsNormSq_block_parseval hP]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single r]
  · rw [projection_mul_matrixGrading hP, Matrix.smul_mul, hP.idempotent,
      hsNormSq_real_smul]
  · intro s _ hsr
    rw [projection_mul_matrixGrading hP, Matrix.smul_mul,
      hP.orthogonal s r hsr, smul_zero, hsNormSq_zero]
  · simp

theorem hsNormSq_matrixGrading_trace (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) :
    hsNormSq (matrixGrading P weight) = ∑ r, weight r ^ 2 * (Matrix.trace (P r)).re := by
  rw [hsNormSq_matrixGrading hP]
  apply Finset.sum_congr rfl
  intro r _
  rw [hsNormSq_projection (P r) (hP.conjTranspose_eq r) (hP.idempotent r)]

theorem sum_hsNormSq_blocks_column (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (r : κ) (hB : B.conjTranspose * B = 1) :
    (∑ s, hsNormSq (P s * B * P r)) = hsNormSq (P r) := by
  calc
    (∑ s, hsNormSq (P s * B * P r)) = hsNormSq (B * P r) := by
      simpa only [Matrix.mul_assoc] using
        (hsNormSq_left_projection_decomposition hP (B * P r)).symm
    _ = hsNormSq (P r) := hsNormSq_mul_left_of_unitary B (P r) hB

theorem sum_hsNormSq_blocks_row (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (s : κ) (hB : B * B.conjTranspose = 1) :
    (∑ r, hsNormSq (P s * B * P r)) = hsNormSq (P s) := by
  rw [← hsNormSq_right_projection_decomposition hP (P s * B)]
  exact hsNormSq_mul_right_of_unitary (P s) B hB

theorem sum_hsNormSq_blocks_column_trace (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (r : κ) (hB : B.conjTranspose * B = 1) :
    (∑ s, hsNormSq (P s * B * P r)) = (Matrix.trace (P r)).re := by
  rw [sum_hsNormSq_blocks_column hP B r hB]
  exact hsNormSq_projection (P r) (hP.conjTranspose_eq r) (hP.idempotent r)

theorem sum_hsNormSq_blocks_row_trace (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (s : κ) (hB : B * B.conjTranspose = 1) :
    (∑ r, hsNormSq (P s * B * P r)) = (Matrix.trace (P s)).re := by
  rw [sum_hsNormSq_blocks_row hP B s hB]
  exact hsNormSq_projection (P s) (hP.conjTranspose_eq s) (hP.idempotent s)

theorem hsNormSq_commutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) :
    hsNormSq (matrixGrading P weight * B - B * matrixGrading P weight) =
      ∑ r, ∑ s, (weight s - weight r) ^ 2 * hsNormSq (P s * B * P r) := by
  rw [hsNormSq_block_parseval hP]
  simp_rw [projection_commutator hP, hsNormSq_real_smul]

theorem hsNormSq_anticommutator (hP : OrthogonalProjectionFamily P)
    (weight : κ → ℝ) (B : Matrix ι ι ℂ) :
    hsNormSq (matrixGrading P weight * B + B * matrixGrading P weight) =
      ∑ r, ∑ s, (weight s + weight r) ^ 2 * hsNormSq (P s * B * P r) := by
  rw [hsNormSq_block_parseval hP]
  simp_rw [projection_anticommutator hP, hsNormSq_real_smul]

/-- The degree grading associated to projections indexed from zero to `n`. -/
def degreeGrading {n : ℕ} (P : Fin (n + 1) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  matrixGrading P fun k => (k.val : ℝ)

/-- The degree grading centered at `n / 2`. -/
def centeredGrading {n : ℕ} (P : Fin (n + 1) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  matrixGrading P fun k => (k.val : ℝ) - (n : ℝ) / 2

theorem hsNormSq_centeredGrading {n : ℕ} {P : Fin (n + 1) → Matrix ι ι ℂ}
    (hP : OrthogonalProjectionFamily P) :
    hsNormSq (centeredGrading P) =
      ∑ k, ((k.val : ℝ) - (n : ℝ) / 2) ^ 2 * hsNormSq (P k) :=
  hsNormSq_matrixGrading hP _

theorem hsNormSq_centeredGrading_trace {n : ℕ} {P : Fin (n + 1) → Matrix ι ι ℂ}
    (hP : OrthogonalProjectionFamily P) :
    hsNormSq (centeredGrading P) =
      ∑ k, ((k.val : ℝ) - (n : ℝ) / 2) ^ 2 * (Matrix.trace (P k)).re :=
  hsNormSq_matrixGrading_trace hP _

theorem centeredGrading_eq {n : ℕ} {P : Fin (n + 1) → Matrix ι ι ℂ}
    (hP : OrthogonalProjectionFamily P) :
    centeredGrading P = degreeGrading P - (((n : ℝ) / 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
  simp only [centeredGrading, degreeGrading, matrixGrading, Complex.ofReal_sub, sub_smul,
    Finset.sum_sub_distrib]
  rw [← Finset.smul_sum, hP.sum_eq_one]

theorem projection_centered_anticommutator {n : ℕ}
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) (r s : Fin (n + 1)) :
    P s * (centeredGrading P * B + B * centeredGrading P) * P r =
      (((s.val : ℝ) + (r.val : ℝ) - n : ℝ) : ℂ) • (P s * B * P r) := by
  rw [centeredGrading, projection_anticommutator hP]
  congr 2
  ring

theorem hsNormSq_centered_anticommutator {n : ℕ}
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (B : Matrix ι ι ℂ) :
    hsNormSq (centeredGrading P * B + B * centeredGrading P) =
      ∑ r, ∑ s, ((s.val : ℝ) + (r.val : ℝ) - n) ^ 2 *
        hsNormSq (P s * B * P r) := by
  rw [hsNormSq_block_parseval hP]
  simp_rw [projection_centered_anticommutator hP, hsNormSq_real_smul]

section OperatorTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Matrix representation of a continuous operator in an orthonormal basis,
bundled with its algebraic compatibility. -/
def operatorMatrixEquiv (b : OrthonormalBasis ι ℂ E) :
    (E →L[ℂ] E) ≃ₐ[ℂ] Matrix ι ι ℂ :=
  (Module.End.toContinuousLinearMap (𝕜 := ℂ) E).symm.trans
    (LinearMap.toMatrixOrthonormal b).toAlgEquiv

/-- Matrix entries for the counting orthonormal basis or any chosen
orthonormal basis. -/
def operatorMatrix (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) : Matrix ι ι ℂ :=
  operatorMatrixEquiv b T

theorem operatorMatrix_eq_toMatrix (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) :
    operatorMatrix b T = LinearMap.toMatrixOrthonormal b T.toLinearMap := rfl

theorem operatorMatrix_apply (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (i j : ι) :
    operatorMatrix b T i j = inner ℂ (b i) (T (b j)) :=
  LinearMap.toMatrixOrthonormal_apply_apply b T.toLinearMap i j

theorem operatorMatrix_injective (b : OrthonormalBasis ι ℂ E) :
    Function.Injective (operatorMatrix b) := (operatorMatrixEquiv b).injective

@[simp]
theorem operatorMatrix_zero (b : OrthonormalBasis ι ℂ E) :
    operatorMatrix b (0 : E →L[ℂ] E) = 0 := map_zero (operatorMatrixEquiv b)

@[simp]
theorem operatorMatrix_one (b : OrthonormalBasis ι ℂ E) :
    operatorMatrix b (1 : E →L[ℂ] E) = 1 := map_one (operatorMatrixEquiv b)

@[simp]
theorem operatorMatrix_add (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    operatorMatrix b (A + B) = operatorMatrix b A + operatorMatrix b B :=
  map_add (operatorMatrixEquiv b) A B

@[simp]
theorem operatorMatrix_sub (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    operatorMatrix b (A - B) = operatorMatrix b A - operatorMatrix b B :=
  map_sub (operatorMatrixEquiv b) A B

@[simp]
theorem operatorMatrix_mul (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    operatorMatrix b (A * B) = operatorMatrix b A * operatorMatrix b B :=
  map_mul (operatorMatrixEquiv b) A B

@[simp]
theorem operatorMatrix_smul (b : OrthonormalBasis ι ℂ E) (z : ℂ) (T : E →L[ℂ] E) :
    operatorMatrix b (z • T) = z • operatorMatrix b T :=
  (operatorMatrixEquiv b).toLinearEquiv.map_smul z T

@[simp]
theorem operatorMatrix_sum (b : OrthonormalBasis ι ℂ E) (T : κ → E →L[ℂ] E) :
    operatorMatrix b (∑ k, T k) = ∑ k, operatorMatrix b (T k) :=
  map_sum (operatorMatrixEquiv b) T Finset.univ

theorem operatorMatrix_isSelfAdjoint (b : OrthonormalBasis ι ℂ E)
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) : IsSelfAdjoint (operatorMatrix b T) := by
  have hlin : IsSelfAdjoint T.toLinearMap :=
    (ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff T).mpr hT
  exact hlin.map (LinearMap.toMatrixOrthonormal b)

/-- Transfer an actually constructed orthogonal family of Hilbert-space
projections to the matrix interface used by the block estimates. -/
theorem orthogonalProjectionFamily_operatorMatrix (b : OrthonormalBasis ι ℂ E)
    (T : κ → E →L[ℂ] E)
    (hself : ∀ k, IsSelfAdjoint (T k))
    (hidem : ∀ k, T k * T k = T k)
    (horth : ∀ r s, r ≠ s → T r * T s = 0)
    (hsum : ∑ k, T k = 1) :
    OrthogonalProjectionFamily (fun k => operatorMatrix b (T k)) where
  selfAdjoint k := operatorMatrix_isSelfAdjoint b (T k) (hself k)
  idempotent k := by rw [← operatorMatrix_mul, hidem k]
  orthogonal r s hrs := by rw [← operatorMatrix_mul, horth r s hrs, operatorMatrix_zero]
  sum_eq_one := by rw [← operatorMatrix_sum, hsum, operatorMatrix_one]

end OperatorTransport

/-- The standard-basis matrix representation is inverse to the standard
Euclidean continuous linear operator associated to a matrix. -/
@[simp]
theorem operatorMatrix_toEuclideanCLM (A : Matrix ι ι ℂ) :
    operatorMatrix (EuclideanSpace.basisFun ι ℂ)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) = A :=
  (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun ι ℂ)).apply_symm_apply A

end LeanBlast.GotsmanLinial

end

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\BlockCoupling.lean

namespace OAI

/-!
# The finite block coupling

Normalize a nonnegative matrix of block masses, identify its two binomial
marginals, and reflect its first index.  The low-degree block vanishing gives
the one-sided displacement bound required by the finite coupling lemma.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

/-- Normalize finite two-index masses by their total mass. -/
noncomputable def normalizedPairWeight {α β : Type*}
    (B : α → β → ℝ) (Z : ℝ) (t : α × β) : ℝ :=
  B t.1 t.2 / Z

theorem normalizedPairWeight_nonneg {α β : Type*}
    (B : α → β → ℝ) (Z : ℝ) (hB : ∀ r s, 0 ≤ B r s) (hZ : 0 ≤ Z)
    (t : α × β) : 0 ≤ normalizedPairWeight B Z t :=
  div_nonneg (hB t.1 t.2) hZ

theorem normalizedPairWeight_row {α β : Type*} [Fintype β]
    (B : α → β → ℝ) (Z : ℝ) (r : α) :
    (∑ s : β, normalizedPairWeight B Z (r, s)) = (∑ s : β, B r s) / Z := by
  simp only [normalizedPairWeight, ← Finset.sum_div]

theorem normalizedPairWeight_column {α β : Type*} [Fintype α]
    (B : α → β → ℝ) (Z : ℝ) (s : β) :
    (∑ r : α, normalizedPairWeight B Z (r, s)) = (∑ r : α, B r s) / Z := by
  simp only [normalizedPairWeight, ← Finset.sum_div]

/-- First-coordinate expectations are computed from the row sums. -/
theorem normalizedPairWeight_expect_fst {α β : Type*} [Fintype α] [Fintype β]
    (B : α → β → ℝ) (Z : ℝ) (φ : α → ℝ) :
    (∑ t : α × β, normalizedPairWeight B Z t * φ t.1) =
      ∑ r : α, ((∑ s : β, B r s) / Z) * φ r := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  simp only [normalizedPairWeight]
  rw [← Finset.sum_mul, ← Finset.sum_div]

/-- Second-coordinate expectations are computed from the column sums. -/
theorem normalizedPairWeight_expect_snd {α β : Type*} [Fintype α] [Fintype β]
    (B : α → β → ℝ) (Z : ℝ) (φ : β → ℝ) :
    (∑ t : α × β, normalizedPairWeight B Z t * φ t.2) =
      ∑ s : β, ((∑ r : α, B r s) / Z) * φ s := by
  rw [Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro s _
  simp only [normalizedPairWeight]
  rw [← Finset.sum_mul, ← Finset.sum_div]

/-- Finite masses with binomial row and column sums, supported above the
anti-diagonal `r+s=n-d`, have the required centered quadratic bound. -/
theorem binomial_block_coupling_bound
    (n d : ℕ) (B : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hB : ∀ r s, 0 ≤ B r s)
    (hrow : ∀ r, (∑ s : Fin (n + 1), B r s) = (n.choose r.val : ℝ))
    (hcol : ∀ s, (∑ r : Fin (n + 1), B r s) = (n.choose s.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → B r s = 0) :
    (∑ r : Fin (n + 1), ∑ s : Fin (n + 1),
      ((s.val : ℝ) + (r.val : ℝ) - (n : ℝ)) ^ 2 * B r s) ≤
        4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n := by
  let w : Fin (n + 1) × Fin (n + 1) → ℝ :=
    normalizedPairWeight B ((2 : ℝ) ^ n)
  let U : Fin (n + 1) × Fin (n + 1) → ℝ := fun t => (t.2.val : ℝ)
  let V : Fin (n + 1) × Fin (n + 1) → ℝ :=
    fun t => (n : ℝ) - (t.1.val : ℝ)
  have hU (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (U t)) =
        ∑ s : Fin (n + 1), binomialWeight n s * φ (s.val : ℝ) := by
    simpa only [w, U, hcol, binomialWeight] using
      normalizedPairWeight_expect_snd B ((2 : ℝ) ^ n)
        (fun s => φ (s.val : ℝ))
  have hV (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (V t)) =
        ∑ r : Fin (n + 1),
          binomialWeight n r * φ ((n : ℝ) - (r.val : ℝ)) := by
    simpa only [w, V, hrow, binomialWeight] using
      normalizedPairWeight_expect_fst B ((2 : ℝ) ^ n)
        (fun r => φ ((n : ℝ) - (r.val : ℝ)))
  have hw : ∀ t, 0 ≤ w t :=
    normalizedPairWeight_nonneg B _ hB (binomialDenominator_pos n).le
  have hprob : (∑ t, w t) = 1 := by
    have h := hU (fun _ => 1)
    simpa only [mul_one, sum_binomialWeight] using h
  have hsame : ∀ φ : ℝ → ℝ,
      (∑ t, w t * φ (U t)) = ∑ t, w t * φ (V t) := by
    intro φ
    rw [hU, hV, binomialWeight_reflect]
  have hvariance :
      (∑ t, w t * (U t - (n : ℝ) / 2) ^ 2) =
        (Real.sqrt (n : ℝ) / 2) ^ 2 := by
    rw [hU (fun z => (z - (n : ℝ) / 2) ^ 2)]
    rw [binomialWeight_variance, binomialSigma_sq]
  have hstep : ∀ t, w t ≠ 0 → V t - U t ≤ (d : ℝ) := by
    rintro ⟨r, s⟩ ht
    have hnonzero : B r s ≠ 0 := by
      intro hz
      exact ht (by simp only [w, normalizedPairWeight, hz, zero_div])
    have hnat : n - d ≤ r.val + s.val :=
      Nat.le_of_not_gt (fun hlt => hnonzero (hvanish r s hlt))
    have hnat' : n ≤ r.val + s.val + d := by omega
    have hreal : (n : ℝ) ≤ (r.val : ℝ) + (s.val : ℝ) + (d : ℝ) := by
      exact_mod_cast hnat'
    dsimp only [U, V]
    linarith
  have hbound := finite_one_sided_coupling_bound w U V
    ((n : ℝ) / 2) (Real.sqrt (n : ℝ) / 2) (d : ℝ)
    hw hprob hsame (binomialSigma_nonneg n) (Nat.cast_nonneg d) hvariance hstep
  calc
    _ = (2 : ℝ) ^ n * (∑ t, w t * (U t - V t) ^ 2) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [w, U, V, normalizedPairWeight]
      field_simp [binomialDenominator_ne_zero n]
      ring
    _ ≤ (2 : ℝ) ^ n * (8 * (d : ℝ) * (Real.sqrt (n : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hbound (binomialDenominator_pos n).le
    _ = 4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n := by ring

/-- The actual finite probability weights supplied by the Hilbert--Schmidt
blocks of an operator in a binomial orthogonal grading. -/
noncomputable def blockCouplingWeight {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin (n + 1) → Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (t : Fin (n + 1) × Fin (n + 1)) : ℝ :=
  normalizedPairWeight (fun r s => hsNormSq (P s * H * P r)) ((2 : ℝ) ^ n) t

theorem blockCouplingWeight_nonneg {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin (n + 1) → Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (t : Fin (n + 1) × Fin (n + 1)) : 0 ≤ blockCouplingWeight P H t :=
  normalizedPairWeight_nonneg _ _ (fun _ _ => hsNormSq_nonneg _)
    (binomialDenominator_pos n).le t

/-- The first block index has the binomial distribution. -/
theorem blockCouplingWeight_fst_marginal {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (H : Matrix ι ι ℂ) (hH : H.conjTranspose * H = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (r : Fin (n + 1)) :
    (∑ s : Fin (n + 1), blockCouplingWeight P H (r, s)) = binomialWeight n r := by
  unfold blockCouplingWeight
  rw [normalizedPairWeight_row, sum_hsNormSq_blocks_column hP H r hH, hmult]
  rfl

/-- The second block index has the same binomial distribution. -/
theorem blockCouplingWeight_snd_marginal {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (H : Matrix ι ι ℂ) (hH : H * H.conjTranspose = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (s : Fin (n + 1)) :
    (∑ r : Fin (n + 1), blockCouplingWeight P H (r, s)) = binomialWeight n s := by
  unfold blockCouplingWeight
  rw [normalizedPairWeight_column, sum_hsNormSq_blocks_row hP H s hH, hmult]
  rfl

/-- Unitarity and the grading multiplicities make the block weights a
probability distribution without any additional normalization assumption. -/
theorem sum_blockCouplingWeight {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (H : Matrix ι ι ℂ) (hH : H.conjTranspose * H = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ)) :
    (∑ t : Fin (n + 1) × Fin (n + 1), blockCouplingWeight P H t) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [blockCouplingWeight_fst_marginal hP H hH hmult]
  exact sum_binomialWeight n

/-- A nonzero block probability lies on or above the required anti-diagonal. -/
theorem blockCouplingWeight_support {n d : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin (n + 1) → Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0)
    (r s : Fin (n + 1)) (ht : blockCouplingWeight P H (r, s) ≠ 0) :
    n - d ≤ r.val + s.val := by
  apply Nat.le_of_not_gt
  intro hlt
  apply ht
  simp only [blockCouplingWeight, normalizedPairWeight, hvanish r s hlt,
    hsNormSq_zero, zero_div]

/-- The spectral block coupling bounds the actual centered grading
anticommutator.  Its hypotheses are the orthogonal grading, its binomial
multiplicities, unitarity, and the separately proved low-degree vanishing. -/
theorem hsNormSq_centeredGrading_anticommutator_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n d : ℕ) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n := by
  rw [hsNormSq_centered_anticommutator hP H]
  apply binomial_block_coupling_bound n d (fun r s => hsNormSq (P s * H * P r))
  · intro r s
    exact hsNormSq_nonneg _
  · intro r
    rw [sum_hsNormSq_blocks_column hP H r hleft, hmult]
  · intro s
    rw [sum_hsNormSq_blocks_row hP H s hright, hmult]
  · intro r s hrs
    rw [hvanish r s hrs, hsNormSq_zero]

/-- Trace-multiplicity form, for direct use with finite-dimensional orthogonal
projections whose ranks have already been computed. -/
theorem hsNormSq_centeredGrading_anticommutator_le_of_trace {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n d : ℕ) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n := by
  apply hsNormSq_centeredGrading_anticommutator_le n d P hP H hleft hright _ hvanish
  intro k
  rw [hsNormSq_projection (P k) (hP.conjTranspose_eq k) (hP.idempotent k), htrace]

end LeanBlast.GotsmanLinial

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\Commutator.lean

namespace OAI

/-!
# Entry bounds for a tridiagonal grading commutator

All norms here are norms of individual complex entries.  No default
norm on a matrix is used.  A complete orthogonal family defines a phase
unitary with eigenvalues `I^k`.  For a tridiagonal operator the commutator is
the difference of two unitary conjugates divided by `2 I`.
-/

noncomputable section

open scoped BigOperators Matrix

namespace LeanBlast.GotsmanLinial

section SpectralMultiplier

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- A complex spectral multiplier for a finite family of projections. -/
def spectralMultiplier (P : κ → Matrix ι ι ℂ) (a : κ → ℂ) : Matrix ι ι ℂ :=
  ∑ k, a k • P k

variable (P : κ → Matrix ι ι ℂ)
variable (hmul : ∀ r s, P r * P s = if r = s then P r else 0)
include hmul

theorem spectralMultiplier_mul_projection (a : κ → ℂ) (r : κ) :
    spectralMultiplier P a * P r = a r • P r := by
  classical
  simp [spectralMultiplier, Finset.sum_mul, hmul]

theorem projection_mul_spectralMultiplier (a : κ → ℂ) (r : κ) :
    P r * spectralMultiplier P a = a r • P r := by
  classical
  simp [spectralMultiplier, Finset.mul_sum, hmul]

theorem spectralMultiplier_mul (a b : κ → ℂ) :
    spectralMultiplier P a * spectralMultiplier P b =
      spectralMultiplier P (fun k => a k * b k) := by
  change spectralMultiplier P a * (∑ k, b k • P k) = _
  rw [Finset.mul_sum]
  simp only [mul_smul_comm, spectralMultiplier_mul_projection P hmul, smul_smul]
  simp only [spectralMultiplier, mul_comm]

omit hmul [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
theorem star_spectralMultiplier (hstar : ∀ k, star (P k) = P k) (a : κ → ℂ) :
    star (spectralMultiplier P a) = spectralMultiplier P (fun k => star (a k)) := by
  simp only [spectralMultiplier, star_sum, star_smul, hstar]

theorem spectralMultiplier_unitary
    (hstar : ∀ k, star (P k) = P k) (hsum : ∑ k, P k = 1)
    (a : κ → ℂ) (ha : ∀ k, a k * star (a k) = 1) :
    spectralMultiplier P a ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_spectralMultiplier P hstar,
    spectralMultiplier_mul P hmul]
  simpa only [spectralMultiplier, ha, one_smul] using hsum

theorem spectralMultiplier_sandwich_block (a b : κ → ℂ)
    (Z : Matrix ι ι ℂ) (r s : κ) :
    P s * (spectralMultiplier P a * Z * spectralMultiplier P b) * P r =
      (a s * b r) • (P s * Z * P r) := by
  calc
    _ = ((P s * spectralMultiplier P a) * Z) *
        (spectralMultiplier P b * P r) := by simp only [mul_assoc]
    _ = ((a s • P s) * Z) * (b r • P r) := by
      rw [projection_mul_spectralMultiplier P hmul,
        spectralMultiplier_mul_projection P hmul]
    _ = _ := by simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

theorem spectralMultiplier_commutator_block (a : κ → ℂ)
    (Z : Matrix ι ι ℂ) (r s : κ) :
    P s * (spectralMultiplier P a * Z - Z * spectralMultiplier P a) * P r =
      (a s - a r) • (P s * Z * P r) := by
  have hleft : P s * (spectralMultiplier P a * Z) * P r =
      a s • (P s * Z * P r) := by
    rw [← mul_assoc (P s) (spectralMultiplier P a) Z,
      projection_mul_spectralMultiplier P hmul]
    simp only [smul_mul_assoc]
  have hright : P s * (Z * spectralMultiplier P a) * P r =
      a r • (P s * Z * P r) := by
    calc
      _ = (P s * Z) * (spectralMultiplier P a * P r) := by simp only [mul_assoc]
      _ = _ := by rw [spectralMultiplier_mul_projection P hmul, mul_smul_comm]
  rw [mul_sub, sub_mul, hleft, hright, sub_smul]

omit hmul [DecidableEq κ] in
theorem spectral_blocks_reconstruct (hsum : ∑ k, P k = 1) (B : Matrix ι ι ℂ) :
    (∑ s, ∑ r, P s * B * P r) = B := by
  simp only [← Finset.mul_sum, hsum, mul_one, ← Finset.sum_mul, one_mul]

omit hmul [DecidableEq κ] in
theorem spectral_blocks_ext (hsum : ∑ k, P k = 1) (A B : Matrix ι ι ℂ)
    (h : ∀ r s, P s * A * P r = P s * B * P r) : A = B := by
  rw [← spectral_blocks_reconstruct P hsum A, ← spectral_blocks_reconstruct P hsum B]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => h r s

end SpectralMultiplier

theorem I_pow_mul_star (k : ℕ) : Complex.I ^ k * star (Complex.I ^ k) = 1 := by
  rw [Complex.star_def, Complex.mul_conj']
  simp

theorem phase_coeff_adjacent (r s : ℕ) (h₁ : s ≤ r + 1) (h₂ : r ≤ s + 1) :
    Complex.I ^ s * star (Complex.I ^ r) - star (Complex.I ^ s) * Complex.I ^ r =
      (2 * Complex.I) * ((s : ℂ) - (r : ℂ)) := by
  have hcases : s = r ∨ s = r + 1 ∨ r = s + 1 := by omega
  rcases hcases with h | h | h
  · subst s
    simp [mul_comm]
  · subst s
    simp only [pow_succ, star_mul, Complex.star_def, Complex.conj_I, Nat.cast_add,
      Nat.cast_one]
    calc
      _ = (2 * Complex.I) * (Complex.I ^ r * star (Complex.I ^ r)) := by
        simp only [Complex.star_def]
        ring
      _ = _ := by rw [I_pow_mul_star]; ring
  · subst r
    simp only [pow_succ, star_mul, Complex.star_def, Complex.conj_I, Nat.cast_add,
      Nat.cast_one]
    calc
      _ = -(2 * Complex.I) * (Complex.I ^ s * star (Complex.I ^ s)) := by
        simp only [Complex.star_def]
        ring
      _ = _ := by rw [I_pow_mul_star]; ring

/-- The difference of two unitary matrices, divided by `2 I`, has entries
of modulus at most one. -/
theorem entry_norm_le_one_of_two_unitaries
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C U V : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hV : V ∈ Matrix.unitaryGroup ι ℂ)
    (h : (2 * Complex.I) • C = U - V) (x y : ι) : ‖C x y‖ ≤ 1 := by
  have heq := congrArg (fun A : Matrix ι ι ℂ => A x y) h
  have hn : (2 : ℝ) * ‖C x y‖ = ‖U x y - V x y‖ := by
    simpa [norm_mul] using congrArg norm heq
  have htri := norm_sub_le (U x y) (V x y)
  have hu₂ := sq_norm_entry_le_one_of_unitary U hU.1 x y
  have hv₂ := sq_norm_entry_le_one_of_unitary V hV.1 x y
  have hu : ‖U x y‖ ≤ 1 := by nlinarith [norm_nonneg (U x y)]
  have hv : ‖V x y‖ ≤ 1 := by nlinarith [norm_nonneg (V x y)]
  linarith

section GradingCommutator

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {P : Fin (n + 1) → Matrix ι ι ℂ}

/-- The spectral phase `I^k` of the degree grading. -/
def gradingPhase (P : Fin (n + 1) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  spectralMultiplier P fun k => Complex.I ^ k.val

theorem gradingPhase_unitary (hP : OrthogonalProjectionFamily P) :
    gradingPhase P ∈ Matrix.unitaryGroup ι ℂ := by
  exact spectralMultiplier_unitary P hP.mul_eq_ite (fun k => (hP.selfAdjoint k).star_eq)
    hP.sum_eq_one _ (fun k => I_pow_mul_star k.val)

/-- Tridiagonality means that blocks at grading distance greater than one vanish. -/
def BlockTridiagonal (P : Fin (n + 1) → Matrix ι ι ℂ) (Z : Matrix ι ι ℂ) : Prop :=
  ∀ r s : Fin (n + 1), (r.val + 1 < s.val ∨ s.val + 1 < r.val) →
    P s * Z * P r = 0

/-- Two opposite phase conjugations differ by `2 I` times the grading commutator. -/
theorem grading_commutator_phase_identity (hP : OrthogonalProjectionFamily P)
    (Z : Matrix ι ι ℂ) (htri : BlockTridiagonal P Z) :
    (2 * Complex.I) • (degreeGrading P * Z - Z * degreeGrading P) =
      gradingPhase P * Z * star (gradingPhase P) -
        star (gradingPhase P) * Z * gradingPhase P := by
  apply projection_block_ext hP
  intro r s
  rw [Matrix.mul_smul, Matrix.smul_mul, degreeGrading, projection_commutator hP,
    Matrix.mul_sub, Matrix.sub_mul]
  simp only [gradingPhase,
    star_spectralMultiplier P (fun k => (hP.selfAdjoint k).star_eq)]
  rw [spectralMultiplier_sandwich_block P hP.mul_eq_ite,
    spectralMultiplier_sandwich_block P hP.mul_eq_ite]
  by_cases hfar : r.val + 1 < s.val ∨ s.val + 1 < r.val
  · simp only [htri r s hfar, smul_zero, sub_self]
  · have hsr : s.val ≤ r.val + 1 := by omega
    have hrs : r.val ≤ s.val + 1 := by omega
    rw [← sub_smul, smul_smul, phase_coeff_adjacent r.val s.val hsr hrs]
    simp

/-- Every entry of the tridiagonal degree commutator has modulus at most one. -/
theorem norm_degreeGrading_commutator_entry_le_one
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ)
    (x y : ι) : ‖(degreeGrading P * Z - Z * degreeGrading P) x y‖ ≤ 1 := by
  have hW := gradingPhase_unitary hP
  have hWstar := Unitary.star_mem hW
  have hU : gradingPhase P * Z * star (gradingPhase P) ∈ Matrix.unitaryGroup ι ℂ :=
    (Matrix.unitaryGroup ι ℂ).mul_mem ((Matrix.unitaryGroup ι ℂ).mul_mem hW hZ) hWstar
  have hV : star (gradingPhase P) * Z * gradingPhase P ∈ Matrix.unitaryGroup ι ℂ :=
    (Matrix.unitaryGroup ι ℂ).mul_mem ((Matrix.unitaryGroup ι ℂ).mul_mem hWstar hZ) hW
  exact entry_norm_le_one_of_two_unitaries _ _ _ hU hV
    (grading_commutator_phase_identity hP Z htri) x y

/-- The Hilbert--Schmidt commutator bound is a consequence of block Parseval
and the fact that each nonzero block has grading distance at most one. -/
theorem hsNormSq_degreeGrading_commutator_le
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) :
    hsNormSq (degreeGrading P * Z - Z * degreeGrading P) ≤ hsNormSq Z := by
  rw [degreeGrading, hsNormSq_commutator hP, hsNormSq_block_parseval hP Z]
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro s _
  by_cases hfar : r.val + 1 < s.val ∨ s.val + 1 < r.val
  · simp only [htri r s hfar, hsNormSq_zero, mul_zero, le_refl]
  · have hsr : (s.val : ℝ) ≤ (r.val : ℝ) + 1 := by
      exact_mod_cast (show s.val ≤ r.val + 1 by omega)
    have hrs : (r.val : ℝ) ≤ (s.val : ℝ) + 1 := by
      exact_mod_cast (show r.val ≤ s.val + 1 by omega)
    have hsq : ((s.val : ℝ) - (r.val : ℝ)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_le]
      constructor <;> linarith
    exact (mul_le_mul_of_nonneg_right hsq (hsNormSq_nonneg _)).trans_eq (one_mul _)

theorem hsNormSq_degreeGrading_commutator_le_card
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ) :
    hsNormSq (degreeGrading P * Z - Z * degreeGrading P) ≤ Fintype.card ι := by
  calc
    _ ≤ hsNormSq Z := hsNormSq_degreeGrading_commutator_le hP Z htri
    _ = _ := hsNormSq_of_unitary Z hZ.1

/-- Centering the grading does not change its commutator. -/
theorem centeredGrading_commutator_eq (hP : OrthogonalProjectionFamily P)
    (Z : Matrix ι ι ℂ) :
    centeredGrading P * Z - Z * centeredGrading P =
      degreeGrading P * Z - Z * degreeGrading P := by
  rw [centeredGrading_eq hP]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  abel

theorem norm_centeredGrading_commutator_entry_le_one
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ)
    (x y : ι) : ‖(centeredGrading P * Z - Z * centeredGrading P) x y‖ ≤ 1 := by
  rw [centeredGrading_commutator_eq hP]
  exact norm_degreeGrading_commutator_entry_le_one hP Z htri hZ x y

theorem sq_norm_centeredGrading_commutator_entry_le_one
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ)
    (x y : ι) : ‖(centeredGrading P * Z - Z * centeredGrading P) x y‖ ^ 2 ≤ 1 := by
  rw [sq_le_one_iff₀ (norm_nonneg _)]
  exact norm_centeredGrading_commutator_entry_le_one hP Z htri hZ x y

theorem hsNormSq_centeredGrading_commutator_le_card
    (hP : OrthogonalProjectionFamily P) (Z : Matrix ι ι ℂ)
    (htri : BlockTridiagonal P Z) (hZ : Z ∈ Matrix.unitaryGroup ι ℂ) :
    hsNormSq (centeredGrading P * Z - Z * centeredGrading P) ≤ Fintype.card ι := by
  rw [centeredGrading_commutator_eq hP]
  exact hsNormSq_degreeGrading_commutator_le_card hP Z htri hZ

end GradingCommutator

end LeanBlast.GotsmanLinial

end

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\CoordinateMultipliers.lean

namespace OAI

/-!
# Actual diagonal sign and coordinate operators on the cube

The matrices here act on the cube with its counting inner product.  Their
continuous linear maps act on `EuclideanSpace`, so all operator-norm statements
refer to the intended Euclidean norm.  The Hilbert--Schmidt statements use the
explicit squared-entry sum `hsNormSq`.
-/

noncomputable section

open scoped BigOperators Matrix

namespace LeanBlast.GotsmanLinial

variable {n : ℕ}

/-- Multiplication by a real function on the cube, represented in the point-mass basis. -/
def signMatrix (h : Cube n → ℝ) : Matrix (Cube n) (Cube n) ℂ :=
  Matrix.diagonal (fun x => (h x : ℂ))

/-- The actual cube coordinate-sign matrix `Z_i`. -/
def coordinateSignMatrix (i : Fin n) : Matrix (Cube n) (Cube n) ℂ :=
  signMatrix (fun x => cubeCoord x i)

@[simp] theorem signMatrix_apply (h : Cube n → ℝ) (x y : Cube n) :
    signMatrix h x y = if x = y then (h x : ℂ) else 0 := by
  simp [signMatrix, Matrix.diagonal_apply]

@[simp] theorem signMatrix_apply_self (h : Cube n → ℝ) (x : Cube n) :
    signMatrix h x x = (h x : ℂ) := by simp

@[simp] theorem coordinateSignMatrix_apply (i : Fin n) (x y : Cube n) :
    coordinateSignMatrix i x y = if x = y then (cubeCoord x i : ℂ) else 0 :=
  signMatrix_apply _ x y

@[simp] theorem signMatrix_conjTranspose (h : Cube n → ℝ) :
    (signMatrix h).conjTranspose = signMatrix h := by
  simp [signMatrix, Matrix.diagonal_conjTranspose]

@[simp] theorem signMatrix_star (h : Cube n → ℝ) :
    star (signMatrix h) = signMatrix h :=
  signMatrix_conjTranspose h

theorem signMatrix_isHermitian (h : Cube n → ℝ) : (signMatrix h).IsHermitian :=
  signMatrix_conjTranspose h

/-- A sign-valued real diagonal is an involution. -/
theorem signMatrix_mul_self (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) : signMatrix h * signMatrix h = 1 := by
  classical
  rw [signMatrix, Matrix.diagonal_mul_diagonal]
  have hs : (fun x => (h x : ℂ) * (h x : ℂ)) = fun _ : Cube n => (1 : ℂ) := by
    funext x
    rcases hh x with hx | hx <;> simp [hx]
  rw [hs, Matrix.diagonal_one]

theorem signMatrix_conjTranspose_mul (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) :
    (signMatrix h).conjTranspose * signMatrix h = 1 := by
  rw [signMatrix_conjTranspose, signMatrix_mul_self h hh]

theorem signMatrix_mul_conjTranspose (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) :
    signMatrix h * (signMatrix h).conjTranspose = 1 := by
  rw [signMatrix_conjTranspose, signMatrix_mul_self h hh]

theorem signMatrix_unitary (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) :
    signMatrix h ∈ Matrix.unitaryGroup (Cube n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, signMatrix_star]
  exact signMatrix_mul_self h hh

/-- A real sign diagonal commutes with every complex diagonal weight. -/
theorem signMatrix_commute_diagonal (h : Cube n → ℝ) (d : Cube n → ℂ) :
    Commute (signMatrix h) (Matrix.diagonal d) := by
  change signMatrix h * Matrix.diagonal d = Matrix.diagonal d * signMatrix h
  simp only [signMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _

theorem signMatrix_mul_diagonal_comm (h : Cube n → ℝ) (d : Cube n → ℂ) :
    signMatrix h * Matrix.diagonal d = Matrix.diagonal d * signMatrix h :=
  (signMatrix_commute_diagonal h d).eq

@[simp] theorem signMatrix_mulVec (h : Cube n → ℝ) (v : Cube n → ℂ) (x : Cube n) :
    (signMatrix h *ᵥ v) x = (h x : ℂ) * v x := by
  simp [signMatrix, Matrix.mulVec_diagonal]

theorem hsNormSq_signMatrix (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) : hsNormSq (signMatrix h) = (2 : ℝ) ^ n := by
  rw [hsNormSq_of_unitary _ (signMatrix_conjTranspose_mul h hh), card_cube]
  simp

@[simp] theorem coordinateSignMatrix_conjTranspose (i : Fin n) :
    (coordinateSignMatrix i).conjTranspose = coordinateSignMatrix i :=
  signMatrix_conjTranspose _

@[simp] theorem coordinateSignMatrix_star (i : Fin n) :
    star (coordinateSignMatrix i) = coordinateSignMatrix i :=
  signMatrix_star _

theorem coordinateSignMatrix_isHermitian (i : Fin n) :
    (coordinateSignMatrix i).IsHermitian := signMatrix_isHermitian _

@[simp] theorem coordinateSignMatrix_mul_self (i : Fin n) :
    coordinateSignMatrix i * coordinateSignMatrix i = 1 :=
  signMatrix_mul_self _ (fun x => cubeCoord_cases x i)

@[simp] theorem coordinateSignMatrix_conjTranspose_mul (i : Fin n) :
    (coordinateSignMatrix i).conjTranspose * coordinateSignMatrix i = 1 := by simp

@[simp] theorem coordinateSignMatrix_mul_conjTranspose (i : Fin n) :
    coordinateSignMatrix i * (coordinateSignMatrix i).conjTranspose = 1 := by simp

theorem coordinateSignMatrix_unitary (i : Fin n) :
    coordinateSignMatrix i ∈ Matrix.unitaryGroup (Cube n) ℂ :=
  signMatrix_unitary _ (fun x => cubeCoord_cases x i)

theorem coordinateSignMatrix_commute_diagonal (i : Fin n) (d : Cube n → ℂ) :
    Commute (coordinateSignMatrix i) (Matrix.diagonal d) :=
  signMatrix_commute_diagonal _ d

theorem coordinateSignMatrix_mul_diagonal_comm (i : Fin n) (d : Cube n → ℂ) :
    coordinateSignMatrix i * Matrix.diagonal d =
      Matrix.diagonal d * coordinateSignMatrix i :=
  (coordinateSignMatrix_commute_diagonal i d).eq

@[simp] theorem coordinateSignMatrix_mulVec (i : Fin n) (v : Cube n → ℂ) (x : Cube n) :
    (coordinateSignMatrix i *ᵥ v) x = (cubeCoord x i : ℂ) * v x :=
  signMatrix_mulVec _ v x

@[simp] theorem hsNormSq_coordinateSignMatrix (i : Fin n) :
    hsNormSq (coordinateSignMatrix i) = (2 : ℝ) ^ n :=
  hsNormSq_signMatrix _ (fun x => cubeCoord_cases x i)

/-- The same diagonal action on the counting-inner-product Euclidean space. -/
def signMultiplier (h : Cube n → ℝ) :
    EuclideanSpace ℂ (Cube n) →L[ℂ] EuclideanSpace ℂ (Cube n) :=
  Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h)

/-- The actual coordinate multiplier on Euclidean space. -/
def coordinateMultiplier (i : Fin n) :
    EuclideanSpace ℂ (Cube n) →L[ℂ] EuclideanSpace ℂ (Cube n) :=
  signMultiplier (fun x => cubeCoord x i)

@[simp] theorem toEuclideanCLM_signMatrix (h : Cube n → ℝ) :
    Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h) = signMultiplier h := rfl

@[simp] theorem toEuclideanCLM_coordinateSignMatrix (i : Fin n) :
    Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (coordinateSignMatrix i) =
      coordinateMultiplier i := rfl

@[simp] theorem signMultiplier_apply (h : Cube n → ℝ)
    (v : EuclideanSpace ℂ (Cube n)) (x : Cube n) :
    signMultiplier h v x = (h x : ℂ) * v x := by
  change (signMatrix h *ᵥ fun y => v y) x = _
  exact signMatrix_mulVec h _ x

@[simp] theorem coordinateMultiplier_apply (i : Fin n)
    (v : EuclideanSpace ℂ (Cube n)) (x : Cube n) :
    coordinateMultiplier i v x = (cubeCoord x i : ℂ) * v x :=
  signMultiplier_apply _ v x

theorem signMultiplier_isSelfAdjoint (h : Cube n → ℝ) :
    IsSelfAdjoint (signMultiplier h) := by
  change star (Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h)) =
    Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h)
  rw [← map_star, signMatrix_star]

theorem coordinateMultiplier_isSelfAdjoint (i : Fin n) :
    IsSelfAdjoint (coordinateMultiplier i) := signMultiplier_isSelfAdjoint _

theorem signMultiplier_mul_self (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) : signMultiplier h * signMultiplier h = 1 := by
  change Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h) *
    Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h) = 1
  rw [← map_mul, signMatrix_mul_self h hh, map_one]

@[simp] theorem coordinateMultiplier_mul_self (i : Fin n) :
    coordinateMultiplier i * coordinateMultiplier i = 1 :=
  signMultiplier_mul_self _ (fun x => cubeCoord_cases x i)

theorem norm_signMultiplier_apply (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) (v : EuclideanSpace ℂ (Cube n)) :
    ‖signMultiplier h v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  rcases hh x with hx | hx <;> simp [signMultiplier_apply, hx]

@[simp] theorem norm_coordinateMultiplier_apply (i : Fin n)
    (v : EuclideanSpace ℂ (Cube n)) : ‖coordinateMultiplier i v‖ = ‖v‖ :=
  norm_signMultiplier_apply _ (fun x => cubeCoord_cases x i) v

theorem norm_signMultiplier_le_one (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) : ‖signMultiplier h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp [norm_signMultiplier_apply h hh]

theorem norm_coordinateMultiplier_le_one (i : Fin n) : ‖coordinateMultiplier i‖ ≤ 1 :=
  norm_signMultiplier_le_one _ (fun x => cubeCoord_cases x i)

end LeanBlast.GotsmanLinial

end

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\CubeOperators.lean

namespace OAI

/-!
# Coordinate commutators and Hamming-distance energy

The coordinate sign matrices are the actual diagonal operators of the Boolean
cube. The identities here turn their Hilbert--Schmidt and entry estimates into
the energy estimates used by the edge-recovery argument.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

variable {n : ℕ}

/-- In the point basis, a coordinate commutator records the difference of the
two endpoint signs. -/
theorem coordinate_commutator_apply
    (M : Matrix (Cube n) (Cube n) ℂ) (i : Fin n) (x y : Cube n) :
    (M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y =
      (((cubeCoord y i - cubeCoord x i : ℝ) : ℂ)) * M x y := by
  simp only [coordinateSignMatrix, signMatrix, Matrix.sub_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Complex.ofReal_sub]
  ring

/-- Squaring a coordinate difference gives four exactly on the coordinates
where the Boolean endpoints differ. -/
theorem coordinate_commutator_sq_norm
    (M : Matrix (Cube n) (Cube n) ℂ) (i : Fin n) (x y : Cube n) :
    ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2 =
      (if x i ≠ y i then (4 : ℝ) else 0) * ‖M x y‖ ^ 2 := by
  rw [coordinate_commutator_apply, norm_mul, mul_pow]
  congr 1
  cases hx : x i <;> cases hy : y i <;> norm_num [cubeCoord, hx, hy]

/-- Summing the squared entries over coordinates counts Hamming distance. -/
theorem sum_coordinate_commutator_sq_norm
    (M : Matrix (Cube n) (Cube n) ℂ) (x y : Cube n) :
    (∑ i : Fin n,
      ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2) =
      4 * (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by
  classical
  simp_rw [coordinate_commutator_sq_norm, ite_mul, zero_mul]
  calc
    (∑ i : Fin n, if x i ≠ y i then 4 * ‖M x y‖ ^ 2 else 0) =
        ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), 4 * ‖M x y‖ ^ 2 := by
      rw [Finset.sum_filter]
    _ = (hammingDist x y : ℝ) * (4 * ‖M x y‖ ^ 2) := by
      simp [hammingDist, nsmul_eq_mul]
    _ = 4 * (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by ring

/-- The total coordinate-commutator energy is four times the distance-weighted
entry energy. -/
theorem sum_hsNormSq_coordinate_commutator
    (M : Matrix (Cube n) (Cube n) ℂ) :
    (∑ i : Fin n, hsNormSq (M * coordinateSignMatrix i - coordinateSignMatrix i * M)) =
      4 * ∑ x : Cube n, ∑ y : Cube n, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by
  classical
  simp only [hsNormSq]
  calc
    (∑ i : Fin n, ∑ x : Cube n, ∑ y : Cube n,
        ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2) =
        ∑ x : Cube n, ∑ y : Cube n, ∑ i : Fin n,
          ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x : Cube n, ∑ y : Cube n,
        4 * (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by
      simp_rw [sum_coordinate_commutator_sq_norm]
    _ = 4 * ∑ x : Cube n, ∑ y : Cube n,
        (hammingDist x y : ℝ) * ‖M x y‖ ^ 2 := by
      simp only [Finset.mul_sum, mul_assoc]

/-- A uniform coordinate-commutator Hilbert--Schmidt bound gives the distance
energy inequality for the actual cube matrix. -/
theorem distance_energy_le_of_coordinate_commutator_bound
    (M : Matrix (Cube n) (Cube n) ℂ)
    (hbound : ∀ i : Fin n,
      hsNormSq (M * coordinateSignMatrix i - coordinateSignMatrix i * M) ≤ (2 : ℝ) ^ n) :
    (∑ x : Cube n, ∑ y : Cube n, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2) ≤
      (n : ℝ) * (2 : ℝ) ^ n / 4 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hbound i)
  rw [sum_hsNormSq_coordinate_commutator] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  linarith

/-- A coordinate at which distinct endpoints differ turns an entrywise
commutator estimate into the edge-entry cap `1/4`. -/
theorem off_diagonal_sq_norm_le_quarter_of_commutator_bound
    (M : Matrix (Cube n) (Cube n) ℂ)
    (hbound : ∀ (i : Fin n) (x y : Cube n),
      ‖(M * coordinateSignMatrix i - coordinateSignMatrix i * M) x y‖ ^ 2 ≤ 1)
    (x y : Cube n) (hxy : x ≠ y) : ‖M x y‖ ^ 2 ≤ (1 : ℝ) / 4 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ y i := by
    by_contra h
    apply hxy
    funext i
    exact not_not.mp (not_exists.mp h i)
  have h := hbound i x y
  rw [coordinate_commutator_sq_norm, if_pos hi] at h
  linarith

end LeanBlast.GotsmanLinial

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\Walsh.lean

namespace OAI

/-!
# Walsh characters of the Boolean cube

The characters are the real sign monomials, regarded as complex-valued
functions.  Counting orthogonality proves linear independence; the cardinality
comparison then gives a basis.  The degree filtration and its dimensions are
constructed from this concrete basis.
-/

noncomputable section

open scoped BigOperators symmDiff
open Finset Submodule Module

namespace LeanBlast.GotsmanLinial

/-- The complex-valued Walsh character associated to a subset of coordinates. -/
def walshChar {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℂ :=
  ∏ i ∈ S, (cubeCoord x i : ℂ)

@[simp] theorem walshChar_empty {n : ℕ} (x : Cube n) :
    walshChar ∅ x = 1 := by simp [walshChar]

@[simp] theorem walshChar_singleton {n : ℕ} (i : Fin n) (x : Cube n) :
    walshChar {i} x = (cubeCoord x i : ℂ) := by simp [walshChar]

theorem walshChar_eq_prod_univ {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walshChar S x = ∏ i : Fin n, if i ∈ S then (cubeCoord x i : ℂ) else 1 := by
  exact (Fintype.prod_ite_mem S (fun i => (cubeCoord x i : ℂ))).symm

@[simp] theorem star_walshChar {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    star (walshChar S x) = walshChar S x := by
  simp [walshChar]

theorem walshChar_mul {n : ℕ} (S T : Finset (Fin n)) (x : Cube n) :
    walshChar S x * walshChar T x = walshChar (S ∆ T) x := by
  classical
  simp only [walshChar_eq_prod_univ, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    cases hx : x i <;> simp [Finset.mem_symmDiff, hS, hT, cubeCoord, hx]

@[simp] theorem walshChar_mul_self {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walshChar S x * walshChar S x = 1 := by
  simpa using walshChar_mul S S x

theorem walshChar_univ_mul {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walshChar Finset.univ x * walshChar S x = walshChar (Finset.univ \ S) x := by
  rw [walshChar_mul]
  congr 1
  ext i
  simp [Finset.mem_symmDiff]

theorem sum_walshChar {n : ℕ} (S : Finset (Fin n)) :
    (∑ x : Cube n, walshChar S x) = if S = ∅ then (2 : ℂ) ^ n else 0 := by
  classical
  have hc (b : Bool) : ((if b then (1 : ℝ) else -1 : ℝ) : ℂ) =
      (if b then (1 : ℂ) else -1) := by cases b <;> simp
  simp_rw [walshChar_eq_prod_univ, cubeCoord, hc]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    if i ∈ S then (if b then (1 : ℂ) else -1) else 1)]
  by_cases hS : S = ∅
  · subst S
    simp
  · rw [if_neg hS]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- Orthogonality for the unnormalized counting inner product. -/
theorem walshChar_orthogonality {n : ℕ} (S T : Finset (Fin n)) :
    (∑ x : Cube n, star (walshChar S x) * walshChar T x) =
      if S = T then (2 : ℂ) ^ n else 0 := by
  simp_rw [star_walshChar, walshChar_mul]
  rw [sum_walshChar]
  simp

/-- Unnormalized Fourier coefficient as a linear functional. -/
def walshCoefficientLinear {n : ℕ} (S : Finset (Fin n)) :
    (Cube n → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ x, star (walshChar S x) * f x
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem walshCoefficientLinear_char {n : ℕ} (S T : Finset (Fin n)) :
    walshCoefficientLinear S (walshChar T) = if S = T then (2 : ℂ) ^ n else 0 :=
  walshChar_orthogonality S T

theorem walshChar_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (walshChar (n := n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc S
  have h := congrArg (walshCoefficientLinear S) hc
  have h' : c S * (2 : ℂ) ^ n = 0 := by
    simpa only [map_sum, map_smul, walshCoefficientLinear_char, map_zero,
      smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h
  exact (mul_eq_zero.mp h').resolve_right (pow_ne_zero _ (by norm_num))

theorem walsh_index_card (n : ℕ) :
    Fintype.card (Finset (Fin n)) = Module.finrank ℂ (Cube n → ℂ) := by
  simp [Module.finrank_fintype_fun_eq_card, Fintype.card_finset, Cube]

/-- The concrete Walsh basis, indexed by coordinate subsets. -/
def walshBasis (n : ℕ) : Basis (Finset (Fin n)) ℂ (Cube n → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (walshChar_linearIndependent n) (walsh_index_card n)

@[simp] theorem walshBasis_apply {n : ℕ} (S : Finset (Fin n)) :
    walshBasis n S = walshChar S := by
  simp [walshBasis]

/-- Functions of Fourier degree at most `k`. -/
def fourierSpace (n k : ℕ) : Submodule ℂ (Cube n → ℂ) :=
  Submodule.span ℂ (walshChar '' {S : Finset (Fin n) | S.card ≤ k})

theorem fourierSpace_mono (n : ℕ) : Monotone (fourierSpace n) := by
  intro k l hkl
  apply Submodule.span_mono
  rintro f ⟨S, hS, rfl⟩
  exact ⟨S, hS.trans hkl, rfl⟩

theorem fourierSpace_eq_top {n k : ℕ} (hk : n ≤ k) : fourierSpace n k = ⊤ := by
  apply top_unique
  rw [← (walshChar_linearIndependent n).span_eq_top_of_card_eq_finrank (walsh_index_card n)]
  apply Submodule.span_mono
  rintro f ⟨S, rfl⟩
  have hS : S.card ≤ n := by simpa using S.card_le_univ
  exact ⟨S, hS.trans hk, rfl⟩

/-- Fourier degree filtration in the Hilbert space with counting inner product. -/
def fourierEuclideanSpace (n k : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Cube n)) :=
  (fourierSpace n k).map
    (WithLp.linearEquiv 2 ℂ (Cube n → ℂ)).symm.toLinearMap

@[simp] theorem mem_fourierEuclideanSpace {n k : ℕ}
    (f : EuclideanSpace ℂ (Cube n)) :
    f ∈ fourierEuclideanSpace n k ↔ (fun x => f x) ∈ fourierSpace n k := by
  change f ∈ (fourierSpace n k).map
    (WithLp.linearEquiv 2 ℂ (Cube n → ℂ)).symm.toLinearMap ↔ _
  rw [Submodule.mem_map_equiv]
  rfl

theorem fourierEuclideanSpace_mono (n : ℕ) : Monotone (fourierEuclideanSpace n) := by
  intro k l hkl
  exact Submodule.map_mono (fourierSpace_mono n hkl)

theorem fourierEuclideanSpace_eq_top {n k : ℕ} (hk : n ≤ k) :
    fourierEuclideanSpace n k = ⊤ := by
  unfold fourierEuclideanSpace
  rw [fourierSpace_eq_top hk, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr
    (WithLp.linearEquiv 2 ℂ (Cube n → ℂ)).symm.surjective

/-- Shift the degree filtration so that its zeroth member is bottom. -/
def fourierFlag (n : ℕ) : ℕ → Submodule ℂ (EuclideanSpace ℂ (Cube n))
  | 0 => ⊥
  | k + 1 => fourierEuclideanSpace n k

@[simp] theorem fourierFlag_zero (n : ℕ) : fourierFlag n 0 = ⊥ := rfl

@[simp] theorem fourierFlag_succ (n k : ℕ) :
    fourierFlag n (k + 1) = fourierEuclideanSpace n k := rfl

theorem fourierFlag_mono (n : ℕ) : Monotone (fourierFlag n) := by
  intro k l hkl
  cases k with
  | zero => exact bot_le
  | succ k =>
    cases l with
    | zero => omega
    | succ l => exact fourierEuclideanSpace_mono n (Nat.le_of_succ_le_succ hkl)

@[simp] theorem fourierFlag_top (n : ℕ) : fourierFlag n (n + 1) = ⊤ :=
  fourierEuclideanSpace_eq_top (le_refl n)

end LeanBlast.GotsmanLinial

end

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\PolynomialDegree.lean

namespace OAI

/-!
# Polynomial degree and the Walsh filtration

The polynomial lemmas concern real multilinear
`MvPolynomial`s. Restriction to the cube is justified by an explicit monomial
expansion rather than assumed as an alternate polynomial representation.
-/

open scoped BigOperators symmDiff

namespace LeanBlast.GotsmanLinial

noncomputable section

variable {n d : ℕ}

/-- Adding a constant preserves the multilinearity condition. -/
theorem IsMultilinear.add_C {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (c : ℝ) : IsMultilinear (p + MvPolynomial.C c) := by
  classical
  intro m hm i
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with hm | hm
  · exact hp m hm i
  · have hm0 : m = 0 := by
      by_cases hc : c = 0
      · simp [hc] at hm
      · simpa [MvPolynomial.support_C, hc] using hm
    simp [hm0]

/-- Adding a constant cannot violate an existing total-degree upper bound. -/
theorem totalDegree_add_C_le {p : MvPolynomial (Fin n) ℝ}
    (hd : p.totalDegree ≤ d) (c : ℝ) :
    (p + MvPolynomial.C c).totalDegree ≤ d := by
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le hd (by simp))

/-- Every exponent occurring in a supported multilinear monomial is one. -/
theorem IsMultilinear.exponent_eq_one {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) {m : Fin n →₀ ℕ} (hm : m ∈ p.support)
    {i : Fin n} (hi : i ∈ m.support) : m i = 1 := by
  exact Nat.le_antisymm (hp m hm i)
    (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

/-- A supported monomial has no more variables than the polynomial's total
degree. This estimate does not require multilinearity. -/
theorem monomial_support_card_le_totalDegree {p : MvPolynomial (Fin n) ℝ}
    {m : Fin n →₀ ℕ} (hm : m ∈ p.support) : m.support.card ≤ p.totalDegree := by
  calc
    m.support.card = ∑ _i ∈ m.support, 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hm

/-- Faithful evaluation of a multilinear polynomial as products over
the supports of its monomials. -/
theorem polynomialValue_eq_multilinear_expansion {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (x : Cube n) :
    polynomialValue p x =
      ∑ m ∈ p.support, p.coeff m * ∏ i ∈ m.support, cubeCoord x i := by
  classical
  unfold polynomialValue
  rw [MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [hp.exponent_eq_one hm hi, pow_one]

/-- The same faithful expansion, with values regarded as complex numbers. -/
theorem polynomialValue_walsh_expansion {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (x : Cube n) :
    (polynomialValue p x : ℂ) =
      ∑ m ∈ p.support, ((p.coeff m : ℝ) : ℂ) * walshChar m.support x := by
  rw [polynomialValue_eq_multilinear_expansion hp]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, walshChar]

/-- A character of degree at most `d` belongs to the corresponding filtration. -/
theorem walshChar_mem_fourierSpace {S : Finset (Fin n)} (hS : S.card ≤ d) :
    walshChar S ∈ fourierSpace n d :=
  Submodule.subset_span ⟨S, hS, rfl⟩

/-- The exact polynomial bridge into the complex Walsh filtration. -/
theorem polynomialValue_mem_fourierSpace {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    (fun x => (polynomialValue p x : ℂ)) ∈ fourierSpace n d := by
  classical
  have hsum : (∑ m ∈ p.support, ((p.coeff m : ℝ) : ℂ) • walshChar m.support) ∈
      fourierSpace n d := by
    apply Submodule.sum_mem
    intro m hm
    exact Submodule.smul_mem _ _
      (walshChar_mem_fourierSpace ((monomial_support_card_le_totalDegree hm).trans hd))
  convert hsum using 1
  ext x
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    polynomialValue_walsh_expansion hp x

/-- Complex conjugation preserves Fourier degree, since each character is real. -/
theorem fourierSpace_star {a : Cube n → ℂ} (ha : a ∈ fourierSpace n d) :
    star a ∈ fourierSpace n d := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨S, hS, rfl⟩ := ha
      have hstar : star (walshChar S) = walshChar S := by
        ext x
        exact star_walshChar S x
      rw [hstar]
      exact walshChar_mem_fourierSpace hS
  | zero => simpa only [star_zero] using (fourierSpace n d).zero_mem
  | add a b _ _ ha hb =>
      simpa only [star_add] using (fourierSpace n d).add_mem ha hb
  | smul c a _ ha =>
      simpa only [star_smul] using (fourierSpace n d).smul_mem (star c) ha

/-- The filtration is multiplicative. The symmetric difference of two index
sets has cardinality at most the sum of their cardinalities. -/
theorem fourierSpace_mul {r s : ℕ} {a b : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (hb : b ∈ fourierSpace n s) :
    a * b ∈ fourierSpace n (r + s) := by
  classical
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem a b ha hb =>
      obtain ⟨S, hS, rfl⟩ := ha
      obtain ⟨T, hT, rfl⟩ := hb
      have hST : (S ∆ T).card ≤ r + s :=
        (Finset.card_le_card Finset.symmDiff_subset_union).trans
          ((Finset.card_union_le S T).trans (Nat.add_le_add hS hT))
      convert walshChar_mem_fourierSpace hST using 1
      ext x
      exact walshChar_mul S T x
  | zero_left b hb => simp
  | zero_right a ha => simp
  | add_left a b c _ _ _ ha hb =>
      simpa only [add_mul] using (fourierSpace n (r + s)).add_mem ha hb
  | add_right a b c _ _ _ ha hb =>
      simpa only [mul_add] using (fourierSpace n (r + s)).add_mem ha hb
  | smul_left c a b _ _ hab =>
      simpa only [smul_mul_assoc] using (fourierSpace n (r + s)).smul_mem c hab
  | smul_right c a b _ _ hab =>
      simpa only [mul_smul_comm] using (fourierSpace n (r + s)).smul_mem c hab

/-- The precise multiplication-conjugation rule used in the weighted pairing. -/
theorem fourierSpace_conj_mul {r s : ℕ} {a b : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (hb : b ∈ fourierSpace n s) :
    (fun x => star (b x) * a x) ∈ fourierSpace n (r + s) := by
  simpa only [Nat.add_comm, Pi.mul_def, Pi.star_def] using
    fourierSpace_mul (fourierSpace_star hb) ha

/-- Multiplication by one cube coordinate raises the degree by at most one. -/
theorem cubeCoord_mul_mem_fourierSpace {r : ℕ} {a : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (i : Fin n) :
    (fun x => (cubeCoord x i : ℂ) * a x) ∈ fourierSpace n (r + 1) := by
  have hi : walshChar {i} ∈ fourierSpace n 1 :=
    walshChar_mem_fourierSpace (by simp)
  have h := fourierSpace_mul hi ha
  rw [Nat.add_comm] at h
  convert h using 1
  ext x
  simp only [Pi.mul_apply, walshChar_singleton]

/-- Functions whose Walsh support starts in degree `k`. -/
def fourierSpaceFrom (n k : ℕ) : Submodule ℂ (Cube n → ℂ) :=
  Submodule.span ℂ (walshChar '' {S : Finset (Fin n) | k ≤ S.card})

theorem walshChar_mem_fourierSpaceFrom {S : Finset (Fin n)} (hS : d ≤ S.card) :
    walshChar S ∈ fourierSpaceFrom n d :=
  Submodule.subset_span ⟨S, hS, rfl⟩

/-- Full parity complements character index sets, taking low degree `d` to
Fourier support in degrees at least `n - d`. -/
theorem parity_mul_mem_fourierSpaceFrom {a : Cube n → ℂ}
    (ha : a ∈ fourierSpace n d) :
    (fun x => walshChar Finset.univ x * a x) ∈ fourierSpaceFrom n (n - d) := by
  classical
  change walshChar Finset.univ * a ∈ fourierSpaceFrom n (n - d)
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨S, hS, rfl⟩ := ha
      have hSc : n - d ≤ (Finset.univ \ S).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
        simpa using Nat.sub_le_sub_left hS n
      convert walshChar_mem_fourierSpaceFrom hSc using 1
      ext x
      exact walshChar_univ_mul S x
  | zero => simp
  | add a b _ _ ha hb =>
      simpa only [mul_add] using (fourierSpaceFrom n (n - d)).add_mem ha hb
  | smul c a _ ha =>
      simpa only [mul_smul_comm] using (fourierSpaceFrom n (n - d)).smul_mem c ha

/-- Low and high Fourier support with a strict gap have zero counting pairing.
There is no conjugation in this formulation because Walsh characters are real;
it applies directly to the product appearing in the weighted proof. -/
theorem sum_mul_eq_zero_of_fourier_separated {r s : ℕ} {a b : Cube n → ℂ}
    (ha : a ∈ fourierSpace n r) (hb : b ∈ fourierSpaceFrom n s) (hrs : r < s) :
    (∑ x : Cube n, a x * b x) = 0 := by
  classical
  induction ha, hb using Submodule.span_induction₂ with
  | mem_mem a b ha hb =>
      obtain ⟨S, hS, rfl⟩ := ha
      obtain ⟨T, hT, rfl⟩ := hb
      have hne : S ≠ T := by
        intro h
        subst T
        exact (not_lt_of_ge (hT.trans hS)) hrs
      simpa only [star_walshChar, if_neg hne] using walshChar_orthogonality S T
  | zero_left b hb => simp
  | zero_right a ha => simp
  | add_left a b c _ _ _ ha hb =>
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha, hb, add_zero]
  | add_right a b c _ _ _ ha hb =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha, hb, add_zero]
  | smul_left c a b _ _ hab =>
      simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_zero] using
        congrArg (fun z : ℂ => c * z) hab
  | smul_right c a b _ _ hab =>
      simpa only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← Finset.mul_sum, mul_zero] using
        congrArg (fun z : ℂ => c * z) hab

/-- The polynomial has high Fourier support after multiplication by
full parity, with no alternate polynomial-class assumption. -/
theorem parity_polynomialValue_mem_fourierSpaceFrom {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    (fun x => walshChar Finset.univ x * (polynomialValue p x : ℂ)) ∈
      fourierSpaceFrom n (n - d) :=
  parity_mul_mem_fourierSpaceFrom (polynomialValue_mem_fourierSpace hp hd)

/-- Every Fourier coefficient below `n - d` of the parity-transformed
polynomial vanishes. -/
theorem parity_polynomialValue_low_coefficient_eq_zero {p : MvPolynomial (Fin n) ℝ}
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) {S : Finset (Fin n)}
    (hS : S.card < n - d) :
    walshCoefficientLinear S
      (fun x => walshChar Finset.univ x * (polynomialValue p x : ℂ)) = 0 := by
  have h := sum_mul_eq_zero_of_fourier_separated
    (walshChar_mem_fourierSpace (Nat.le_refl S.card))
    (parity_polynomialValue_mem_fourierSpaceFrom hp hd) hS
  simpa only [walshCoefficientLinear, LinearMap.coe_mk, AddHom.coe_mk, star_walshChar] using h

end

end LeanBlast.GotsmanLinial

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\SignParity.lean

namespace OAI

/-!
# Removing threshold zeros and turning sensitive edges into constant-sign edges

All graph pairs are ordered. The cube coordinates are the real
signs encoded by `Bool` in the public statement.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

/-- Full parity, with values in the reals. -/
noncomputable def fullParity {n : ℕ} (x : Cube n) : ℝ :=
  ∏ i : Fin n, cubeCoord x i

/-- Two cube vertices differ by a single coordinate flip. -/
def CubeAdjacent {n : ℕ} (x y : Cube n) : Prop :=
  ∃ i : Fin n, flip i x = y

/-- All ordered pairs of neighboring vertices. -/
noncomputable def orderedNeighborPairs (n : ℕ) : Finset (Cube n × Cube n) := by
  classical
  exact Finset.univ.filter fun e => hammingDist e.1 e.2 = 1

/-- Ordered neighboring pairs at which a real function has equal values. -/
noncomputable def orderedConstantEdges {n : ℕ} (h : Cube n → ℝ) :
    Finset (Cube n × Cube n) := by
  classical
  exact (orderedNeighborPairs n).filter fun e => h e.1 = h e.2

private theorem exists_pos_lt_finset {α : Type*} (s : Finset α) (a : α → ℝ)
    (ha : ∀ x ∈ s, 0 < a x) : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s, ε < a x := by
  classical
  revert ha
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨1, by norm_num, by simp⟩
  | @insert x s hx ih =>
      intro ha
      obtain ⟨ε, hε, hεa⟩ := ih (fun y hy => ha y (Finset.mem_insert_of_mem hy))
      have hax : 0 < a x := ha x (Finset.mem_insert_self x s)
      refine ⟨min ε (a x / 2), lt_min hε (by linarith), ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_left _ _) (hεa y hy)

/-- A positive constant removes all zeros of a real function on a finite set
without changing its threshold signs, including the convention `sign(0)=1`. -/
theorem exists_pos_shift_nonzero_preserves_sign {α : Type*} [Fintype α]
    (v : α → ℝ) : ∃ ε : ℝ, 0 < ε ∧ (∀ x, v x + ε ≠ 0) ∧
      (∀ x, thresholdSign (v x + ε) = thresholdSign (v x)) := by
  classical
  let a : α → ℝ := fun x => if v x < 0 then -v x else 1
  have ha : ∀ x ∈ (Finset.univ : Finset α), 0 < a x := by
    intro x _
    by_cases hx : v x < 0
    · simp [a, hx, neg_pos.mpr hx]
    · simp [a, hx]
  obtain ⟨ε, hε, hεa⟩ := exists_pos_lt_finset Finset.univ a ha
  have hneg : ∀ x, v x < 0 → v x + ε < 0 := by
    intro x hx
    have he : ε < -v x := by simpa [a, hx] using hεa x (Finset.mem_univ x)
    linarith
  refine ⟨ε, hε, ?_, ?_⟩
  · intro x
    by_cases hx : v x < 0
    · exact ne_of_lt (hneg x hx)
    · exact ne_of_gt (add_pos_of_nonneg_of_pos (le_of_not_gt hx) hε)
  · intro x
    by_cases hx : v x < 0
    · simp [thresholdSign, not_le.mpr hx, not_le.mpr (hneg x hx)]
    · have hv : 0 ≤ v x := le_of_not_gt hx
      simp [thresholdSign, hv, add_nonneg hv hε.le]

@[simp] theorem fullParity_sq {n : ℕ} (x : Cube n) : fullParity x ^ 2 = 1 := by
  rw [fullParity, ← Finset.prod_pow]
  simp

theorem fullParity_cases {n : ℕ} (x : Cube n) :
    fullParity x = 1 ∨ fullParity x = -1 :=
  sq_eq_one_iff.mp (fullParity_sq x)

/-- Reversing one coordinate reverses full parity. -/
@[simp] theorem fullParity_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    fullParity (flip i x) = -fullParity x := by
  classical
  have hc : cubeCoord (flip i x) = Function.update (cubeCoord x) i (-cubeCoord x i) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [cubeCoord_flip_ne x i j hj, Function.update_of_ne hj]
  unfold fullParity
  rw [hc, Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase, neg_mul,
    Finset.mul_prod_erase Finset.univ (cubeCoord x) (Finset.mem_univ i)]

@[simp] theorem hammingDist_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    hammingDist x (flip i x) = 1 := by
  classical
  have hset : (Finset.univ.filter fun j => x j ≠ flip i x j) = {i} := by
    ext j
    by_cases hj : j = i
    · subst j
      cases hx : x i <;> simp [flip, hx]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      simp [flip, hj]
  simp only [hammingDist, hset, Finset.card_singleton]

/-- The flip definition of adjacency agrees with Hamming distance one. -/
theorem adjacent_iff_hammingDist_eq_one {n : ℕ} (x y : Cube n) :
    CubeAdjacent x y ↔ hammingDist x y = 1 := by
  classical
  constructor
  · rintro ⟨i, rfl⟩
    exact hammingDist_flip i x
  · intro hxy
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hxy
    refine ⟨i, ?_⟩
    funext j
    by_cases hj : j = i
    · subst j
      have hmem : i ∈ Finset.univ.filter (fun j => x j ≠ y j) := by rw [hi]; simp
      have hneq : x i ≠ y i := (Finset.mem_filter.mp hmem).2
      rw [flip_apply_same]
      cases hx : x i <;> cases hy : y i <;> simp_all
    · have heq : x j = y j := by
        by_contra hneq
        have hmem : j ∈ Finset.univ.filter (fun j => x j ≠ y j) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hneq⟩
        rw [hi] at hmem
        exact hj (Finset.mem_singleton.mp hmem)
      rw [flip_apply_ne i x j hj, heq]

/-- A vertex and a direction identify a unique ordered cube edge. -/
def directedEdgeEmbedding (n : ℕ) : (Fin n × Cube n) ↪ (Cube n × Cube n) where
  toFun e := (e.2, flip e.1 e.2)
  inj' := by
    rintro ⟨i, x⟩ ⟨j, y⟩ heq
    have hxy : x = y := congrArg Prod.fst heq
    subst y
    have hij : i = j := flip_injective_direction x (congrArg Prod.snd heq)
    subst j
    rfl

theorem orderedNeighborPairs_eq_map {n : ℕ} :
    orderedNeighborPairs n = Finset.univ.map (directedEdgeEmbedding n) := by
  classical
  ext e
  constructor
  · intro he
    have hd : hammingDist e.1 e.2 = 1 := (Finset.mem_filter.mp he).2
    obtain ⟨i, hi⟩ := (adjacent_iff_hammingDist_eq_one e.1 e.2).mpr hd
    exact Finset.mem_map.mpr ⟨(i, e.1), Finset.mem_univ _, Prod.ext rfl hi⟩
  · intro he
    obtain ⟨⟨i, x⟩, _, rfl⟩ := Finset.mem_map.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hammingDist_flip i x⟩

/-- The `n * 2^n` count includes both orientations of every cube edge. -/
theorem card_orderedNeighborPairs (n : ℕ) :
    (orderedNeighborPairs n).card = n * 2 ^ n := by
  rw [orderedNeighborPairs_eq_map]
  simp

theorem card_orderedConstantEdges {n : ℕ} (h : Cube n → ℝ) :
    (orderedConstantEdges h).card =
      ∑ i : Fin n, (Finset.univ.filter fun x => h x = h (flip i x)).card := by
  classical
  unfold orderedConstantEdges
  rw [orderedNeighborPairs_eq_map, Finset.filter_map, Finset.card_map]
  change (Finset.univ.filter fun e : Fin n × Cube n => h e.2 = h (flip e.1 e.2)).card = _
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Fintype.sum_prod_type _

/-- Twisting a sign-valued function by parity changes sensitivity into
equality across a coordinate flip. -/
theorem parity_twist_eq_iff {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) (i : Fin n) (x : Cube n) :
    fullParity x * f x = fullParity (flip i x) * f (flip i x) ↔
      f x ≠ f (flip i x) := by
  rw [fullParity_flip]
  rcases fullParity_cases x with hp | hp <;>
    rcases hf x with hx | hx <;>
    rcases hf (flip i x) with hy | hy <;> norm_num [hp, hx, hy]

theorem parity_twist_cases {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) (x : Cube n) :
    fullParity x * f x = 1 ∨ fullParity x * f x = -1 := by
  rcases fullParity_cases x with hp | hp <;>
    rcases hf x with hx | hx <;> simp [hp, hx]

theorem card_orderedConstantEdges_parity {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) :
    (orderedConstantEdges (fun x => fullParity x * f x)).card = sensitiveEdgeCount f := by
  classical
  rw [card_orderedConstantEdges]
  unfold sensitiveEdgeCount
  apply Finset.sum_congr rfl
  intro i _
  unfold sensitiveVertices
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x _
  exact parity_twist_eq_iff hf i x

/-- Exact uniform normalization: both sides count each sensitive undirected
edge twice, once in each direction. -/
theorem averageSensitivity_eq_parity_edges {n : ℕ} {f : Cube n → ℝ}
    (hf : ∀ x, f x = 1 ∨ f x = -1) :
    averageSensitivity f =
      ((orderedConstantEdges (fun x => fullParity x * f x)).card : ℝ) / (2 : ℝ) ^ n := by
  rw [averageSensitivity_eq_count, card_orderedConstantEdges_parity hf]

theorem polynomialThreshold_sensitivity_eq_parity_edges {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) :
    averageSensitivity (polynomialThreshold p) =
      ((orderedConstantEdges (fun x => fullParity x * polynomialThreshold p x)).card : ℝ) /
        (2 : ℝ) ^ n :=
  averageSensitivity_eq_parity_edges (fun x => thresholdSign_cases (polynomialValue p x))

/-- The real parity used for threshold signs is exactly the full complex
Walsh character under the standard real embedding. -/
@[simp] theorem ofReal_fullParity {n : ℕ} (x : Cube n) :
    (fullParity x : ℂ) = walshChar Finset.univ x := by
  simp only [fullParity, Complex.ofReal_prod, walshChar]

@[simp] theorem polynomialValue_add_C {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (ε : ℝ) (x : Cube n) :
    polynomialValue (p + MvPolynomial.C ε) x = polynomialValue p x + ε := by
  simp [polynomialValue]

/-- The zero-removal reduction preserves multilinearity, the degree bound,
and the entire threshold function. -/
theorem exists_nonzero_polynomial_same_threshold {n d : ℕ}
    {p : MvPolynomial (Fin n) ℝ} (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    ∃ q : MvPolynomial (Fin n) ℝ,
      IsMultilinear q ∧ q.totalDegree ≤ d ∧
        (∀ x : Cube n, polynomialValue q x ≠ 0) ∧
        polynomialThreshold q = polynomialThreshold p := by
  obtain ⟨ε, _hε, hnonzero, hsign⟩ :=
    exists_pos_shift_nonzero_preserves_sign (polynomialValue p)
  refine ⟨p + MvPolynomial.C ε, hp.add_C ε, totalDegree_add_C_le hd ε, ?_, ?_⟩
  · intro x
    simpa only [polynomialValue_add_C] using hnonzero x
  · funext x
    simpa only [polynomialThreshold, polynomialValue_add_C] using hsign x

end LeanBlast.GotsmanLinial

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\EdgeRecovery.lean

namespace OAI

/-!
# Recovering constant-sign edges from grading energy

The counting argument is separated from construction of the grading matrix.
Its hypotheses are explicit entrywise, total-energy, and distance-energy facts.
No edge-count or anticommutator conclusion is assumed.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- A finite distance layer, also useful for weights indexed by ordered pairs. -/
def distanceShell (d : α → ℕ) (k : ℕ) : Finset α :=
  Finset.univ.filter fun a => d a = k

@[simp] theorem mem_distanceShell (d : α → ℕ) (k : ℕ) (a : α) :
    a ∈ distanceShell d k ↔ d a = k := by
  simp [distanceShell]

/-- Pointwise distance counting: distance-zero entries are the only possible
source of a deficit between total mass and distance-weighted mass. -/
theorem twice_mass_sub_neighbor_le_distance (d : α → ℕ) (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    2 * (∑ a, w a) - (∑ a ∈ distanceShell d 1, w a) ≤
      2 * (∑ a ∈ distanceShell d 0, w a) + ∑ a, (d a : ℝ) * w a := by
  have hpoint : ∀ a,
      2 * w a - (if d a = 1 then w a else 0) ≤
        2 * (if d a = 0 then w a else 0) + (d a : ℝ) * w a := by
    intro a
    by_cases h0 : d a = 0
    · simp [h0]
    by_cases h1 : d a = 1
    · rw [if_pos h1, if_neg h0, h1]
      norm_num
      linarith
    have h2 : 2 ≤ d a := by omega
    have h2R : (2 : ℝ) ≤ (d a : ℝ) := by exact_mod_cast h2
    simpa only [if_neg h0, if_neg h1, sub_zero, mul_zero, zero_add] using
      mul_le_mul_of_nonneg_right h2R (hw a)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun a _ => hpoint a
  simpa only [distanceShell, Finset.sum_filter, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum] using hsum

/-- The sum of the nonnegative neighbor deficits is controlled by twice the
distance-zero energy. Equivalently, `A₀ + F ≤ 2 A₀`. -/
theorem neighbor_deficit_le_twice_zero_mass (d : α → ℕ) (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (htotal : (∑ a, w a) = ((distanceShell d 1).card : ℝ) / 4)
    (henergy : (∑ a, (d a : ℝ) * w a) ≤ ∑ a, w a) :
    (∑ a ∈ distanceShell d 1, ((1 / 4 : ℝ) - w a)) ≤
      2 * (∑ a ∈ distanceShell d 0, w a) := by
  have hpoint := twice_mass_sub_neighbor_le_distance d w hw
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  linarith

/-- Restricting the nonnegative deficits to any chosen neighbor subset gives
the counting bound needed before applying the anticommutator identity. -/
theorem selected_neighbor_card_le_eight_mass (d : α → ℕ) (w : α → ℝ)
    (s : Finset α) (hs : s ⊆ distanceShell d 1)
    (hw : ∀ a, 0 ≤ w a)
    (hcap : ∀ a ∈ distanceShell d 1, w a ≤ (1 / 4 : ℝ))
    (htotal : (∑ a, w a) = ((distanceShell d 1).card : ℝ) / 4)
    (henergy : (∑ a, (d a : ℝ) * w a) ≤ ∑ a, w a) :
    (s.card : ℝ) ≤ 8 * ((∑ a ∈ distanceShell d 0, w a) + ∑ a ∈ s, w a) := by
  have hrestrict := Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun a ha _ => sub_nonneg.mpr (hcap a ha))
  have hdeficit := neighbor_deficit_le_twice_zero_mass d w hw htotal henergy
  have hmass : 0 ≤ ∑ a ∈ s, w a := Finset.sum_nonneg fun a _ => hw a
  have hselected : (∑ a ∈ s, ((1 / 4 : ℝ) - w a)) =
      (s.card : ℝ) / 4 - ∑ a ∈ s, w a := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hselected] at hrestrict
  linarith

/-- On an equal-sign pair the anticommutator has four times the squared entry
mass. The diagonal is included as an equal-sign pair. -/
theorem anticommutator_entry_sq_of_same_sign [DecidableEq ι]
    (M : Matrix ι ι ℂ) (h : ι → ℝ) (hh : ∀ i, h i = 1 ∨ h i = -1)
    (i j : ι) (hij : h i = h j) :
    ‖(M * Matrix.diagonal (fun i => (h i : ℂ)) +
      Matrix.diagonal (fun i => (h i : ℂ)) * M) i j‖ ^ 2 =
      4 * ‖M i j‖ ^ 2 := by
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [← hij]
  have hfactor : M i j * (h i : ℂ) + (h i : ℂ) * M i j =
      (2 : ℂ) * (h i : ℂ) * M i j := by ring
  rw [hfactor]
  have hnorm : ‖(h i : ℂ)‖ = 1 := by
    rcases hh i with hi | hi <;> simp [hi]
  rw [norm_mul, norm_mul, hnorm]
  norm_num [mul_pow]

/-- The diagonal and a disjoint set of equal-sign neighbor entries contribute
four times their mass to the Hilbert--Schmidt squared norm. -/
theorem anticommutator_energy_ge_selected [DecidableEq ι]
    (ρ : ι → ι → ℕ) (hzero : ∀ i j, ρ i j = 0 → i = j)
    (M : Matrix ι ι ℂ) (h : ι → ℝ) (hh : ∀ i, h i = 1 ∨ h i = -1)
    (s : Finset (ι × ι))
    (hs : s ⊆ distanceShell (fun p : ι × ι => ρ p.1 p.2) 1)
    (hsign : ∀ p ∈ s, h p.1 = h p.2) :
    4 * ((∑ p ∈ distanceShell (fun p : ι × ι => ρ p.1 p.2) 0,
        ‖M p.1 p.2‖ ^ 2) + ∑ p ∈ s, ‖M p.1 p.2‖ ^ 2) ≤
      hsNormSq (M * Matrix.diagonal (fun i => (h i : ℂ)) +
        Matrix.diagonal (fun i => (h i : ℂ)) * M) := by
  classical
  let D := distanceShell (fun p : ι × ι => ρ p.1 p.2) 0
  let T := M * Matrix.diagonal (fun i => (h i : ℂ)) +
    Matrix.diagonal (fun i => (h i : ℂ)) * M
  have hdisj : Disjoint D s := by
    apply Finset.disjoint_left.mpr
    intro p hpD hps
    have h0 : ρ p.1 p.2 = 0 := by simpa only [D, mem_distanceShell] using hpD
    have h1 : ρ p.1 p.2 = 1 := by simpa only [mem_distanceShell] using hs hps
    omega
  have hsame : ∀ p ∈ D ∪ s, h p.1 = h p.2 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpD | hps
    · have h0 : ρ p.1 p.2 = 0 := by simpa only [D, mem_distanceShell] using hpD
      rw [hzero _ _ h0]
    · exact hsign p hps
  have hentries : (∑ p ∈ D ∪ s, 4 * ‖M p.1 p.2‖ ^ 2) =
      ∑ p ∈ D ∪ s, ‖T p.1 p.2‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro p hp
    exact (anticommutator_entry_sq_of_same_sign M h hh p.1 p.2 (hsame p hp)).symm
  have hsubset : (∑ p ∈ D ∪ s, ‖T p.1 p.2‖ ^ 2) ≤
      ∑ p : ι × ι, ‖T p.1 p.2‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun p _ _ => sq_nonneg ‖T p.1 p.2‖)
  have hsplit : (∑ p ∈ D ∪ s, 4 * ‖M p.1 p.2‖ ^ 2) =
      4 * ((∑ p ∈ D, ‖M p.1 p.2‖ ^ 2) + ∑ p ∈ s, ‖M p.1 p.2‖ ^ 2) := by
    rw [Finset.sum_union hdisj, ← Finset.mul_sum, ← Finset.mul_sum, mul_add]
  rw [← hentries, hsplit] at hsubset
  simpa only [D, T, hsNormSq, Fintype.sum_prod_type] using hsubset

/-- Abstract edge recovery from the exact finite matrix energy hypotheses.
The chosen set may be any subset of constant-sign distance-one pairs. -/
theorem edge_recovery_for_subset [DecidableEq ι]
    (ρ : ι → ι → ℕ) (hzero : ∀ i j, ρ i j = 0 → i = j)
    (M : Matrix ι ι ℂ) (h : ι → ℝ) (hh : ∀ i, h i = 1 ∨ h i = -1)
    (s : Finset (ι × ι))
    (hs : s ⊆ distanceShell (fun p : ι × ι => ρ p.1 p.2) 1)
    (hsign : ∀ p ∈ s, h p.1 = h p.2)
    (hcap : ∀ i j, ρ i j = 1 → ‖M i j‖ ^ 2 ≤ (1 / 4 : ℝ))
    (htotal : hsNormSq M =
      ((distanceShell (fun p : ι × ι => ρ p.1 p.2) 1).card : ℝ) / 4)
    (henergy : (∑ i, ∑ j, (ρ i j : ℝ) * ‖M i j‖ ^ 2) ≤ hsNormSq M) :
    (s.card : ℝ) ≤ 2 * hsNormSq
      (M * Matrix.diagonal (fun i => (h i : ℂ)) +
        Matrix.diagonal (fun i => (h i : ℂ)) * M) := by
  have hcount := selected_neighbor_card_le_eight_mass
    (fun p : ι × ι => ρ p.1 p.2) (fun p => ‖M p.1 p.2‖ ^ 2) s hs
    (fun p => sq_nonneg _) (fun p hp => hcap p.1 p.2 (by simpa only [mem_distanceShell] using hp))
    (by simpa only [hsNormSq, Fintype.sum_prod_type] using htotal)
    (by simpa only [hsNormSq, Fintype.sum_prod_type] using henergy)
  have hanti := anticommutator_energy_ge_selected ρ hzero M h hh s hs hsign
  linarith

/-- The edge-recovery inequality on the Boolean cube, from the three
matrix facts established by the grading and commutator constructions. -/
theorem edge_recovery {n : ℕ} (M : Matrix (Cube n) (Cube n) ℂ)
    (h : Cube n → ℝ) (hh : ∀ x, h x = 1 ∨ h x = -1)
    (htotal : hsNormSq M = (n : ℝ) * (2 : ℝ) ^ n / 4)
    (hdistance : (∑ x, ∑ y, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2) ≤ hsNormSq M)
    (hcap : ∀ x y, x ≠ y → ‖M x y‖ ^ 2 ≤ (1 / 4 : ℝ)) :
    ((orderedConstantEdges h).card : ℝ) ≤
      2 * hsNormSq (M * Matrix.diagonal (fun x => (h x : ℂ)) +
        Matrix.diagonal (fun x => (h x : ℂ)) * M) := by
  classical
  apply edge_recovery_for_subset (fun x y : Cube n => hammingDist x y)
    (fun _ _ hxy => hammingDist_eq_zero.mp hxy) M h hh (orderedConstantEdges h)
  · exact Finset.filter_subset _ _
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro x y hxy
    apply hcap x y
    intro heq
    subst y
    simp only [hammingDist_self, Nat.zero_ne_one] at hxy
  · change hsNormSq M = ((orderedNeighborPairs n).card : ℝ) / 4
    rw [card_orderedNeighborPairs]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using htotal
  · exact hdistance

end LeanBlast.GotsmanLinial

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\ProjectionTrace.lean

namespace OAI

/-!
# Traces of actual orthogonal projections

The trace calculation uses the algebraic theorem for a projection onto a
submodule. In particular, no spectral decomposition or matrix norm instance
is needed. Matrix transport is valid in every basis, and hence in the
orthonormal basis used for the weighted grading.
-/

noncomputable section

namespace LeanBlast.GotsmanLinial

section General

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- The actual orthogonal projection is algebraically a projection onto its
specified submodule. -/
theorem starProjection_isProj (K : Submodule 𝕜 E) :
    LinearMap.IsProj K K.starProjection.toLinearMap where
  map_mem := K.starProjection_apply_mem
  map_id := fun _ hx => Submodule.starProjection_eq_self_iff.mpr hx

/-- The trace of the actual orthogonal projection is the dimension of its range. -/
theorem trace_starProjection (K : Submodule 𝕜 E) :
    LinearMap.trace 𝕜 E K.starProjection.toLinearMap = (Module.finrank 𝕜 K : 𝕜) :=
  (starProjection_isProj K).trace

variable [Fintype ι] [DecidableEq ι]

/-- The matrix trace of an orthogonal projection is independent of the chosen basis. -/
theorem trace_toMatrix_starProjection (b : Module.Basis ι 𝕜 E) (K : Submodule 𝕜 E) :
    Matrix.trace (LinearMap.toMatrix b b K.starProjection.toLinearMap) =
      (Module.finrank 𝕜 K : 𝕜) := by
  rw [← LinearMap.trace_eq_matrix_trace 𝕜 b, trace_starProjection]

/-- The orthonormal matrix representation used by the grading has the correct trace. -/
theorem trace_toMatrixOrthonormal_starProjection (b : OrthonormalBasis ι 𝕜 E)
    (K : Submodule 𝕜 E) :
    Matrix.trace (LinearMap.toMatrixOrthonormal b K.starProjection.toLinearMap) =
      (Module.finrank 𝕜 K : 𝕜) :=
  trace_toMatrix_starProjection b.toBasis K

end General

section Complex

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

/-- The real trace required by Hilbert--Schmidt block-mass computations. -/
theorem re_trace_toMatrixOrthonormal_starProjection (b : OrthonormalBasis ι ℂ E)
    (K : Submodule ℂ E) :
    (Matrix.trace (LinearMap.toMatrixOrthonormal b K.starProjection.toLinearMap)).re =
      (Module.finrank ℂ K : ℝ) := by
  rw [trace_toMatrixOrthonormal_starProjection]
  simp

end Complex

end LeanBlast.GotsmanLinial

end

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\WalshDimensions.lean

namespace OAI

/-!
Dimensions of the Walsh degree filtration, derived from the
linear independence of the concrete characters.
-/

noncomputable section

open scoped BigOperators
open Module

namespace LeanBlast.GotsmanLinial

/-- Count low-degree character indices by partitioning them according to cardinality. -/
theorem card_finset_card_le (n k : ℕ) :
    Fintype.card {S : Finset (Fin n) // S.card ≤ k} =
      ∑ j ∈ Finset.range (k + 1), n.choose j := by
  classical
  let e : {S : Finset (Fin n) // S.card ≤ k} ≃
      (Σ j : Fin (k + 1), {S : Finset (Fin n) // S.card = j.val}) := {
    toFun := fun S => ⟨⟨S.val.card, Nat.lt_succ_of_le S.property⟩, ⟨S.val, rfl⟩⟩
    invFun := fun a => ⟨a.2.val, by
      rw [a.2.property]
      exact Nat.le_of_lt_succ a.1.isLt⟩
    left_inv := fun S => by rfl
    right_inv := fun a => by
      rcases a with ⟨⟨j, hj⟩, ⟨S, hS⟩⟩
      dsimp at hS
      subst j
      rfl
  }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_finset_len, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range _ _

/-- The dimension of the degree-`k` Fourier subspace is the number of indices of
cardinality at most `k`. This formula remains valid beyond the saturated stage. -/
theorem fourierSpace_finrank (n k : ℕ) :
    finrank ℂ (fourierSpace n k) = ∑ j ∈ Finset.range (k + 1), n.choose j := by
  classical
  rw [fourierSpace, Set.image_eq_range]
  calc
    _ = Fintype.card {S : Finset (Fin n) // S.card ≤ k} := by
      exact finrank_span_eq_card ((walshChar_linearIndependent n).comp
        (Subtype.val : {S : Finset (Fin n) // S.card ≤ k} → Finset (Fin n))
        Subtype.val_injective)
    _ = _ := card_finset_card_le n k

/-- Each new degree contributes exactly the next binomial multiplicity. -/
theorem fourierSpace_finrank_add (n k : ℕ) :
    finrank ℂ (fourierSpace n k) + n.choose (k + 1) =
      finrank ℂ (fourierSpace n (k + 1)) := by
  simp only [fourierSpace_finrank]
  exact (Finset.sum_range_succ (fun j => n.choose j) (k + 1)).symm

theorem fourierSpace_finrank_sub (n k : ℕ) :
    finrank ℂ (fourierSpace n (k + 1)) - finrank ℂ (fourierSpace n k) =
      n.choose (k + 1) := by
  rw [← fourierSpace_finrank_add]
  exact Nat.add_sub_cancel_left _ _

@[simp] theorem fourierSpace_zero_finrank (n : ℕ) :
    finrank ℂ (fourierSpace n 0) = 1 := by
  simp [fourierSpace_finrank]

/-- At or above degree `n`, the Fourier space has the full cube dimension. -/
theorem fourierSpace_finrank_of_le {n k : ℕ} (hnk : n ≤ k) :
    finrank ℂ (fourierSpace n k) = 2 ^ n := by
  rw [fourierSpace_eq_top hnk, finrank_top]
  simp [Module.finrank_fintype_fun_eq_card]

/-- Arbitrary invertible linear changes of coordinates preserve every Fourier dimension. -/
theorem map_fourierSpace_finrank {E : Type*} [AddCommGroup E] [Module ℂ E]
    (n k : ℕ) (D : (Cube n → ℂ) ≃ₗ[ℂ] E) :
    finrank ℂ ((fourierSpace n k).map D.toLinearMap) =
      ∑ j ∈ Finset.range (k + 1), n.choose j := by
  rw [D.finrank_map_eq, fourierSpace_finrank]

/-- Passing to the counting Euclidean Hilbert space changes no dimensions. -/
theorem fourierEuclideanSpace_finrank (n k : ℕ) :
    finrank ℂ (fourierEuclideanSpace n k) =
      ∑ j ∈ Finset.range (k + 1), n.choose j := by
  exact map_fourierSpace_finrank n k (WithLp.linearEquiv 2 ℂ (Cube n → ℂ)).symm

/-- With the bottom stage inserted, stage `k` contains exactly degrees below `k`. -/
theorem fourierFlag_finrank (n k : ℕ) :
    finrank ℂ (fourierFlag n k) = ∑ j ∈ Finset.range k, n.choose j := by
  cases k with
  | zero =>
      rw [fourierFlag_zero, finrank_bot]
      simp
  | succ k => exact fourierEuclideanSpace_finrank n k

/-- The degree-`k` layer has the prescribed binomial dimension increment. -/
theorem fourierFlag_finrank_add (n k : ℕ) :
    finrank ℂ (fourierFlag n k) + n.choose k =
      finrank ℂ (fourierFlag n (k + 1)) := by
  simp only [fourierFlag_finrank]
  exact (Finset.sum_range_succ (fun j => n.choose j) k).symm

theorem fourierFlag_finrank_sub (n k : ℕ) :
    finrank ℂ (fourierFlag n (k + 1)) - finrank ℂ (fourierFlag n k) =
      n.choose k := by
  rw [← fourierFlag_finrank_add]
  exact Nat.add_sub_cancel_left _ _

/-- Any invertible weight preserves the dimensions of all stages of the Euclidean flag. -/
theorem map_fourierFlag_finrank (n k : ℕ)
    (D : EuclideanSpace ℂ (Cube n) ≃ₗ[ℂ] EuclideanSpace ℂ (Cube n)) :
    finrank ℂ ((fourierFlag n k).map D.toLinearMap) =
      ∑ j ∈ Finset.range k, n.choose j := by
  rw [D.finrank_map_eq, fourierFlag_finrank]

/-- In particular, an invertible weight preserves each binomial dimension increment. -/
theorem map_fourierFlag_finrank_add (n k : ℕ)
    (D : EuclideanSpace ℂ (Cube n) ≃ₗ[ℂ] EuclideanSpace ℂ (Cube n)) :
    finrank ℂ ((fourierFlag n k).map D.toLinearMap) + n.choose k =
      finrank ℂ ((fourierFlag n (k + 1)).map D.toLinearMap) := by
  rw [D.finrank_map_eq, D.finrank_map_eq]
  exact fourierFlag_finrank_add n k

end LeanBlast.GotsmanLinial

end

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\WeightedGrading.lean

namespace OAI

/-!
# The actual weighted orthogonal grading of the cube

The construction first orthogonalizes an arbitrary finite flag of subspaces.
It then transports the concrete Walsh flag by the invertible square-root
weight and takes the orthogonal projections in the counting Hilbert space.
The resulting matrices are proved to form an orthogonal decomposition of
the identity with the prescribed binomial multiplicities.
-/

noncomputable section

open scoped BigOperators
open Module

namespace LeanBlast.GotsmanLinial

section FiniteFlag

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local instance : CompleteSpace E := FiniteDimensional.complete 𝕜 E

/-- The new orthogonal layer appearing between two consecutive stages of a flag. -/
def flagLayer (K : ℕ → Submodule 𝕜 E) (k : ℕ) : Submodule 𝕜 E :=
  K (k + 1) ⊓ (K k)ᗮ

/-- The actual orthogonal projection onto a layer of a finite-dimensional flag. -/
def flagProjection (K : ℕ → Submodule 𝕜 E) (k : ℕ) : E →L[𝕜] E :=
  (flagLayer K k).starProjection

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_le_next (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    flagLayer K k ≤ K (k + 1) := inf_le_left

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_le_prev_orthogonal (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    flagLayer K k ≤ (K k)ᗮ := inf_le_right

theorem flagLayer_sup_prev (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (k : ℕ) :
    K k ⊔ flagLayer K k = K (k + 1) := by
  simpa only [flagLayer, inf_comm] using
    Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (hK (Nat.le_succ k))

theorem flagLayer_finrank_add (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (k : ℕ) :
    finrank 𝕜 (K k) + finrank 𝕜 (flagLayer K k) = finrank 𝕜 (K (k + 1)) := by
  change finrank 𝕜 (K k) + finrank 𝕜 (K (k + 1) ⊓ (K k)ᗮ : Submodule 𝕜 E) = _
  rw [inf_comm]
  exact Submodule.finrank_add_inf_finrank_orthogonal (hK (Nat.le_succ k))

theorem flagLayer_finrank (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (k : ℕ) :
    finrank 𝕜 (flagLayer K k) = finrank 𝕜 (K (k + 1)) - finrank 𝕜 (K k) := by
  have h := flagLayer_finrank_add K hK k
  omega

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_isOrtho_of_lt (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    {r s : ℕ} (hrs : r < s) : flagLayer K r ⟂ flagLayer K s := by
  apply Submodule.IsOrtho.symm
  exact (flagLayer_le_prev_orthogonal K s).trans
    (Submodule.orthogonal_le ((flagLayer_le_next K r).trans (hK hrs)))

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_isOrtho (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    {r s : ℕ} (hrs : r ≠ s) : flagLayer K r ⟂ flagLayer K s := by
  rcases lt_or_gt_of_ne hrs with h | h
  · exact flagLayer_isOrtho_of_lt K hK h
  · exact (flagLayer_isOrtho_of_lt K hK h).symm

theorem flagLayer_iSup_eq_top (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    (hzero : K 0 = ⊥) (n : ℕ) (htop : K (n + 1) = ⊤) :
    (⨆ k : Fin (n + 1), flagLayer K k.val) = ⊤ := by
  let S := ⨆ k : Fin (n + 1), flagLayer K k.val
  have hle : ∀ m, m ≤ n + 1 → K m ≤ S := by
    intro m
    induction m with
    | zero => simp [hzero]
    | succ m ih =>
      intro hm
      rw [← flagLayer_sup_prev K hK m]
      exact sup_le (ih (by omega))
        (le_iSup (fun k : Fin (n + 1) => flagLayer K k.val) ⟨m, by omega⟩)
  apply top_unique
  rw [← htop]
  exact hle (n + 1) le_rfl

omit [FiniteDimensional 𝕜 E] in
theorem flagLayer_orthogonalFamily (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    (n : ℕ) :
    OrthogonalFamily 𝕜 (fun k : Fin (n + 1) => flagLayer K k.val)
      (fun k => (flagLayer K k.val).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro r s hrs
  exact flagLayer_isOrtho K hK (fun h => hrs (Fin.ext h))

theorem flagProjection_isSelfAdjoint (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    IsSelfAdjoint (flagProjection K k) :=
  isSelfAdjoint_starProjection (flagLayer K k)

theorem flagProjection_idempotent (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    flagProjection K k * flagProjection K k = flagProjection K k :=
  (flagLayer K k).isIdempotentElem_starProjection.eq

theorem flagProjection_mul_eq_zero (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    {r s : ℕ} (hrs : r ≠ s) : flagProjection K r * flagProjection K s = 0 :=
  (flagLayer_isOrtho K hK hrs).starProjection_comp_starProjection

theorem sum_flagProjection (K : ℕ → Submodule 𝕜 E) (hK : Monotone K)
    (hzero : K 0 = ⊥) (n : ℕ) (htop : K (n + 1) = ⊤) :
    (∑ k : Fin (n + 1), flagProjection K k.val) = 1 := by
  ext x
  change (∑ k : Fin (n + 1), (flagLayer K k.val).starProjection) x = x
  rw [sum_apply]
  apply (flagLayer_orthogonalFamily K hK n).sum_projection_of_mem_iSup
  rw [flagLayer_iSup_eq_top K hK hzero n htop]
  trivial

@[simp]
theorem range_flagProjection (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    (flagProjection K k).range = flagLayer K k :=
  Submodule.range_starProjection (flagLayer K k)

theorem flagProjection_apply_mem_next (K : ℕ → Submodule 𝕜 E) (k : ℕ) (x : E) :
    flagProjection K k x ∈ K (k + 1) :=
  (flagLayer K k).starProjection_apply_mem x |>.1

theorem flagProjection_apply_eq_zero_of_mem_prev (K : ℕ → Submodule 𝕜 E)
    (k : ℕ) {x : E} (hx : x ∈ K k) : flagProjection K k x = 0 := by
  have ho : x ∈ (flagLayer K k)ᗮ :=
    Submodule.orthogonal_le (flagLayer_le_prev_orthogonal K k)
      ((K k).le_orthogonal_orthogonal hx)
  exact congrArg Subtype.val
    (Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr ho)

end FiniteFlag

section InvertibleWeights

variable {Ω : Type*} [Fintype Ω]

/-- Multiplication by pointwise nonzero coefficients is a linear equivalence. -/
def coordinateMulEquiv (a : Ω → ℂ) (ha : ∀ x, a x ≠ 0) :
    (Ω → ℂ) ≃ₗ[ℂ] (Ω → ℂ) where
  toFun f x := a x * f x
  invFun f x := (a x)⁻¹ * f x
  left_inv f := by
    funext x
    simp only [← mul_assoc, inv_mul_cancel₀ (ha x), one_mul]
  right_inv f := by
    funext x
    simp only [← mul_assoc, mul_inv_cancel₀ (ha x), one_mul]
  map_add' f g := by
    funext x
    exact mul_add _ _ _
  map_smul' c f := by
    funext x
    exact mul_left_comm _ _ _

/-- Multiplication by the square root of a strictly positive weight, in the
counting Euclidean Hilbert space. -/
def sqrtWeightEquiv (w : Ω → ℝ) (hw : ∀ x, 0 < w x) :
    EuclideanSpace ℂ Ω ≃ₗ[ℂ] EuclideanSpace ℂ Ω :=
  ((WithLp.linearEquiv 2 ℂ (Ω → ℂ)).trans
    (coordinateMulEquiv (fun x => (Real.sqrt (w x) : ℂ))
      (fun x => Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (hw x)))))).trans
    (WithLp.linearEquiv 2 ℂ (Ω → ℂ)).symm

omit [Fintype Ω] in
@[simp]
theorem sqrtWeightEquiv_apply (w : Ω → ℝ) (hw : ∀ x, 0 < w x)
    (f : EuclideanSpace ℂ Ω) (x : Ω) :
    sqrtWeightEquiv w hw f x = (Real.sqrt (w x) : ℂ) * f x := rfl

omit [Fintype Ω] in
@[simp]
theorem sqrtWeightEquiv_symm_apply (w : Ω → ℝ) (hw : ∀ x, 0 < w x)
    (f : EuclideanSpace ℂ Ω) (x : Ω) :
    (sqrtWeightEquiv w hw).symm f x = (Real.sqrt (w x) : ℂ)⁻¹ * f x := rfl

end InvertibleWeights

section Transport

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- Transport a degree flag through an invertible linear weight operator. -/
def transportFlag (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E) (k : ℕ) :
    Submodule 𝕜 E := (F k).map D.toLinearMap

theorem transportFlag_monotone (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E)
    (hF : Monotone F) : Monotone (transportFlag D F) := by
  intro i j hij
  exact Submodule.map_mono (hF hij)

theorem transportFlag_zero (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E)
    (hF : F 0 = ⊥) : transportFlag D F 0 = ⊥ := by
  simp [transportFlag, hF]

theorem transportFlag_top (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E)
    (k : ℕ) (hF : F k = ⊤) : transportFlag D F k = ⊤ := by
  simp [transportFlag, hF]

theorem transportFlag_finrank (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E) (k : ℕ) :
    finrank 𝕜 (transportFlag D F k) = finrank 𝕜 (F k) :=
  D.finrank_map_eq (F k)

/-- The weighted construction preserves every prescribed dimension increment. -/
theorem transportFlag_layer_finrank [FiniteDimensional 𝕜 E] (D : E ≃ₗ[𝕜] E)
    (F : ℕ → Submodule 𝕜 E) (hF : Monotone F) (k d : ℕ)
    (hd : finrank 𝕜 (F k) + d = finrank 𝕜 (F (k + 1))) :
    finrank 𝕜 (flagLayer (transportFlag D F) k) = d := by
  have h := flagLayer_finrank_add (transportFlag D F) (transportFlag_monotone D F hF) k
  rw [transportFlag_finrank, transportFlag_finrank] at h
  omega

end Transport

section MatrixTransport

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Matrix of an actual flag-layer projection in an orthonormal basis. -/
def flagProjectionMatrix (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (k : ℕ) : Matrix ι ι ℂ :=
  operatorMatrix b (flagProjection K k)

/-- The matrix projection-family laws follow from the constructed Hilbert-space
projections, without any additional grading hypothesis. -/
theorem flagProjectionMatrix_family (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (hK : Monotone K) (hzero : K 0 = ⊥)
    (n : ℕ) (htop : K (n + 1) = ⊤) :
    OrthogonalProjectionFamily (fun k : Fin (n + 1) => flagProjectionMatrix b K k.val) :=
  orthogonalProjectionFamily_operatorMatrix b
    (fun k : Fin (n + 1) => flagProjection K k.val)
    (fun k => flagProjection_isSelfAdjoint K k.val)
    (fun k => flagProjection_idempotent K k.val)
    (fun _ _ hrs => flagProjection_mul_eq_zero K hK (fun h => hrs (Fin.ext h)))
    (sum_flagProjection K hK hzero n htop)

theorem trace_flagProjectionMatrix (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (k : ℕ) :
    Matrix.trace (flagProjectionMatrix b K k) = (finrank ℂ (flagLayer K k) : ℂ) :=
  trace_toMatrixOrthonormal_starProjection b (flagLayer K k)

theorem re_trace_flagProjectionMatrix (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (k : ℕ) :
    (Matrix.trace (flagProjectionMatrix b K k)).re = (finrank ℂ (flagLayer K k) : ℝ) :=
  re_trace_toMatrixOrthonormal_starProjection b (flagLayer K k)

end MatrixTransport

section WeightedCube

variable {n : ℕ}

/-- The weighted degree-`k` subspace of the counting Hilbert space. -/
def weightedFourierSpace (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (k : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Cube n)) :=
  (fourierEuclideanSpace n k).map (sqrtWeightEquiv w hw).toLinearMap

/-- The weighted Fourier flag, shifted by one so that stage zero is bottom. -/
def weightedFourierFlag (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    ℕ → Submodule ℂ (EuclideanSpace ℂ (Cube n)) :=
  transportFlag (sqrtWeightEquiv w hw) (fourierFlag n)

@[simp]
theorem weightedFourierFlag_zero (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    weightedFourierFlag w hw 0 = ⊥ :=
  transportFlag_zero _ _ (fourierFlag_zero n)

@[simp]
theorem weightedFourierFlag_succ (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (k : ℕ) :
    weightedFourierFlag w hw (k + 1) = weightedFourierSpace w hw k := rfl

theorem weightedFourierFlag_mono (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    Monotone (weightedFourierFlag w hw) :=
  transportFlag_monotone _ _ (fourierFlag_mono n)

@[simp]
theorem weightedFourierFlag_top (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    weightedFourierFlag w hw (n + 1) = ⊤ :=
  transportFlag_top _ _ _ (fourierFlag_top n)

/-- Weighting preserves the exact binomial dimensions of the orthogonal layers. -/
theorem weightedFourierFlag_layer_finrank (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : ℕ) :
    finrank ℂ (flagLayer (weightedFourierFlag w hw) k) = n.choose k :=
  transportFlag_layer_finrank (sqrtWeightEquiv w hw) (fourierFlag n)
    (fourierFlag_mono n) k (n.choose k) (fourierFlag_finrank_add n k)

/-- Actual orthogonal projection onto weighted Fourier layer `k`. -/
def weightedProjection (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (k : Fin (n + 1)) :
    EuclideanSpace ℂ (Cube n) →L[ℂ] EuclideanSpace ℂ (Cube n) :=
  flagProjection (weightedFourierFlag w hw) k.val

/-- The projection represented in the point-mass orthonormal basis. -/
def weightedProjectionMatrix (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) : Matrix (Cube n) (Cube n) ℂ :=
  flagProjectionMatrix (EuclideanSpace.basisFun (Cube n) ℂ)
    (weightedFourierFlag w hw) k.val

theorem weightedProjection_apply_mem (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) (f : EuclideanSpace ℂ (Cube n)) :
    weightedProjection w hw k f ∈ weightedFourierSpace w hw k.val :=
  flagProjection_apply_mem_next (weightedFourierFlag w hw) k.val f

theorem weightedProjection_annihilate_prev (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) {f : EuclideanSpace ℂ (Cube n)}
    (hf : f ∈ weightedFourierFlag w hw k.val) : weightedProjection w hw k f = 0 :=
  flagProjection_apply_eq_zero_of_mem_prev (weightedFourierFlag w hw) k.val hf

theorem weightedProjectionMatrix_family (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    OrthogonalProjectionFamily (weightedProjectionMatrix w hw) :=
  flagProjectionMatrix_family (EuclideanSpace.basisFun (Cube n) ℂ)
    (weightedFourierFlag w hw) (weightedFourierFlag_mono w hw)
    (weightedFourierFlag_zero w hw) n (weightedFourierFlag_top w hw)

theorem weightedProjectionMatrix_trace (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) :
    Matrix.trace (weightedProjectionMatrix w hw k) = (n.choose k.val : ℂ) := by
  rw [weightedProjectionMatrix, trace_flagProjectionMatrix, weightedFourierFlag_layer_finrank]

theorem weightedProjectionMatrix_trace_re (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) :
    (Matrix.trace (weightedProjectionMatrix w hw k)).re = (n.choose k.val : ℝ) := by
  rw [weightedProjectionMatrix_trace]
  simp

theorem weightedProjectionMatrix_hsNormSq (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) : hsNormSq (weightedProjectionMatrix w hw k) = (n.choose k.val : ℝ) := by
  rw [hsNormSq_projection _ ((weightedProjectionMatrix_family w hw).conjTranspose_eq k)
    ((weightedProjectionMatrix_family w hw).idempotent k)]
  exact weightedProjectionMatrix_trace_re w hw k

/-- Every real diagonal multiplier commutes with the positive square-root weight. -/
theorem sqrtWeightEquiv_commute_signMultiplier
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (h : Cube n → ℝ)
    (f : EuclideanSpace ℂ (Cube n)) :
    signMultiplier h (sqrtWeightEquiv w hw f) =
      sqrtWeightEquiv w hw (signMultiplier h f) := by
  ext x
  simp only [signMultiplier_apply, sqrtWeightEquiv_apply]
  exact mul_left_comm _ _ _

theorem sqrtWeightEquiv_commute_coordinateMultiplier
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (i : Fin n)
    (f : EuclideanSpace ℂ (Cube n)) :
    coordinateMultiplier i (sqrtWeightEquiv w hw f) =
      sqrtWeightEquiv w hw (coordinateMultiplier i f) :=
  sqrtWeightEquiv_commute_signMultiplier w hw (fun x => cubeCoord x i) f

end WeightedCube

end LeanBlast.GotsmanLinial

end

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\CoordinateDegree.lean

namespace OAI

/-!
# Coordinate multiplication raises the Fourier degree by at most one

The unweighted polynomial degree bound is transported to the actual diagonal matrices and continuous linear operators
on the counting-inner-product Euclidean space, including the shifted flag used
by the weighted grading construction.
-/

noncomputable section

open scoped Matrix

namespace LeanBlast.GotsmanLinial

variable {n k : ℕ}

/-- The actual coordinate-sign matrix raises the unweighted degree by at most one. -/
theorem coordinateSignMatrix_mem_fourierSpace (i : Fin n) {a : Cube n → ℂ}
    (ha : a ∈ fourierSpace n k) :
    coordinateSignMatrix i *ᵥ a ∈ fourierSpace n (k + 1) := by
  change (fun x => (coordinateSignMatrix i *ᵥ a) x) ∈ fourierSpace n (k + 1)
  simpa only [coordinateSignMatrix_mulVec] using cubeCoord_mul_mem_fourierSpace ha i

/-- The continuous coordinate multiplier has the same degree shift in Euclidean space. -/
theorem coordinateMultiplier_mem_fourierEuclideanSpace (i : Fin n)
    {a : EuclideanSpace ℂ (Cube n)} (ha : a ∈ fourierEuclideanSpace n k) :
    coordinateMultiplier i a ∈ fourierEuclideanSpace n (k + 1) := by
  apply (mem_fourierEuclideanSpace _).2
  simpa only [coordinateMultiplier_apply] using
    cubeCoord_mul_mem_fourierSpace ((mem_fourierEuclideanSpace _).1 ha) i

/-- Submodule-map form of the Euclidean coordinate-degree shift. -/
theorem coordinateMultiplier_map_fourierEuclideanSpace_le (i : Fin n) :
    (fourierEuclideanSpace n k).map (coordinateMultiplier i).toLinearMap ≤
      fourierEuclideanSpace n (k + 1) := by
  rintro a ⟨b, hb, rfl⟩
  exact coordinateMultiplier_mem_fourierEuclideanSpace i hb

/-- The shifted flag also has a one-step coordinate shift, including its bottom term. -/
theorem coordinateMultiplier_fourierFlag_shift (i : Fin n) :
    ∀ k (a : EuclideanSpace ℂ (Cube n)), a ∈ fourierFlag n k →
      coordinateMultiplier i a ∈ fourierFlag n (k + 1) := by
  intro k a ha
  cases k with
  | zero =>
      have ha0 : a = 0 := by simpa using ha
      simp [ha0]
  | succ k =>
      exact coordinateMultiplier_mem_fourierEuclideanSpace i ha

end LeanBlast.GotsmanLinial

end

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\GradingShift.lean

namespace OAI

/-!
# A degree shift is tridiagonal in the associated orthogonal grading

These lemmas retain the degree-shift premise explicitly. The cube application
discharges it using coordinate multiplication and the weighted Fourier flag.
-/

noncomputable section

namespace LeanBlast.GotsmanLinial

section FiniteFlag

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local instance : CompleteSpace E := FiniteDimensional.complete 𝕜 E

/-- An operator that raises the flag index by at most one has no blocks
strictly above the first off-diagonal. -/
theorem flagProjection_mul_shift_eq_zero
    (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (Z : E →L[𝕜] E)
    (hshift : ∀ k x, x ∈ K k → Z x ∈ K (k + 1))
    {r s : ℕ} (hrs : r + 1 < s) :
    flagProjection K s * Z * flagProjection K r = 0 := by
  ext x
  change flagProjection K s (Z (flagProjection K r x)) = 0
  apply flagProjection_apply_eq_zero_of_mem_prev
  exact hK (by omega : r + 1 + 1 ≤ s)
    (hshift (r + 1) (flagProjection K r x) (flagProjection_apply_mem_next K r x))

/-- Self-adjointness gives the other half of the band by taking adjoints. -/
theorem flagProjection_tridiagonal
    (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (Z : E →L[𝕜] E)
    (hZ : IsSelfAdjoint Z)
    (hshift : ∀ k x, x ∈ K k → Z x ∈ K (k + 1))
    {r s : ℕ} (hrs : r + 1 < s ∨ s + 1 < r) :
    flagProjection K s * Z * flagProjection K r = 0 := by
  rcases hrs with hrs | hsr
  · exact flagProjection_mul_shift_eq_zero K hK Z hshift hrs
  · have h := congrArg star (flagProjection_mul_shift_eq_zero K hK Z hshift hsr)
    simpa only [star_mul, star_zero, (flagProjection_isSelfAdjoint K r).star_eq,
      (flagProjection_isSelfAdjoint K s).star_eq, hZ.star_eq, mul_assoc] using h

/-- The band property is preserved by taking matrices or any other ring
representation of the operator algebra. -/
theorem map_flagProjection_tridiagonal
    {A : Type*} [Ring A] (F : (E →L[𝕜] E) →+* A)
    (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (Z : E →L[𝕜] E)
    (hZ : IsSelfAdjoint Z)
    (hshift : ∀ k x, x ∈ K k → Z x ∈ K (k + 1))
    {r s : ℕ} (hrs : r + 1 < s ∨ s + 1 < r) :
    F (flagProjection K s) * F Z * F (flagProjection K r) = 0 := by
  rw [← map_mul, ← map_mul, flagProjection_tridiagonal K hK Z hZ hshift hrs, map_zero]

omit [FiniteDimensional 𝕜 E] in
/-- Commutation transports a degree-shift statement through a weight map. -/
theorem shift_mem_map_of_commute
    (V : ℕ → Submodule 𝕜 E) (D Z : E →ₗ[𝕜] E)
    (hcommute : ∀ x, Z (D x) = D (Z x))
    (hshift : ∀ k x, x ∈ V k → Z x ∈ V (k + 1))
    (k : ℕ) {x : E} (hx : x ∈ (V k).map D) :
    Z x ∈ (V (k + 1)).map D := by
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨Z y, hshift k y hy, (hcommute y).symm⟩

end FiniteFlag

section MatrixFlag

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- The concrete matrix form consumed by the commutator estimate. -/
theorem operatorMatrix_flagProjection_tridiagonal
    (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (hK : Monotone K) (Z : E →L[ℂ] E)
    (hZ : IsSelfAdjoint Z)
    (hshift : ∀ k x, x ∈ K k → Z x ∈ K (k + 1))
    (n : ℕ) (r s : Fin (n + 1))
    (hrs : r.val + 1 < s.val ∨ s.val + 1 < r.val) :
    operatorMatrix b (flagProjection K s.val) * operatorMatrix b Z *
      operatorMatrix b (flagProjection K r.val) = 0 := by
  exact map_flagProjection_tridiagonal (operatorMatrixEquiv b).toRingHom
    K hK Z hZ hshift hrs

end MatrixFlag

section WeightedCube

variable {n : ℕ}

/-- Coordinate signs commute with the actual positive square-root weight. -/
theorem coordinateMultiplier_sqrtWeight_commute
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (i : Fin n)
    (a : EuclideanSpace ℂ (Cube n)) :
    coordinateMultiplier i (sqrtWeightEquiv w hw a) =
      sqrtWeightEquiv w hw (coordinateMultiplier i a) := by
  ext x
  simp only [coordinateMultiplier_apply, sqrtWeightEquiv_apply]
  exact mul_left_comm _ _ _

/-- The actual weighted Fourier flag retains the one-step coordinate shift. -/
theorem coordinateMultiplier_weightedFlag_shift
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (i : Fin n) :
    ∀ k (a : EuclideanSpace ℂ (Cube n)),
      a ∈ transportFlag (sqrtWeightEquiv w hw) (fourierFlag n) k →
      coordinateMultiplier i a ∈
        transportFlag (sqrtWeightEquiv w hw) (fourierFlag n) (k + 1) := by
  intro k a ha
  exact shift_mem_map_of_commute (fourierFlag n) (sqrtWeightEquiv w hw).toLinearMap
    (coordinateMultiplier i).toLinearMap
    (coordinateMultiplier_sqrtWeight_commute w hw i)
    (coordinateMultiplier_fourierFlag_shift i) k ha

/-- Tridiagonality for the actually constructed weighted Fourier projections,
expressed in an arbitrary orthonormal coordinate system. -/
theorem weightedFlag_operatorMatrix_tridiagonal
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (b : OrthonormalBasis (Cube n) ℂ (EuclideanSpace ℂ (Cube n)))
    (i : Fin n) (r s : Fin (n + 1))
    (hrs : r.val + 1 < s.val ∨ s.val + 1 < r.val) :
    flagProjectionMatrix b (transportFlag (sqrtWeightEquiv w hw) (fourierFlag n)) s.val *
      operatorMatrix b (coordinateMultiplier i) *
      flagProjectionMatrix b (transportFlag (sqrtWeightEquiv w hw) (fourierFlag n)) r.val = 0 := by
  exact operatorMatrix_flagProjection_tridiagonal b
    (transportFlag (sqrtWeightEquiv w hw) (fourierFlag n))
    (transportFlag_monotone _ _ (fourierFlag_mono n))
    (coordinateMultiplier i) (coordinateMultiplier_isSelfAdjoint i)
    (coordinateMultiplier_weightedFlag_shift w hw i) n r s hrs

/-- The raw coordinate-sign matrices are tridiagonal for the actual weighted
Fourier projection family. There is no remaining degree-shift hypothesis. -/
theorem weightedProjectionMatrix_tridiagonal
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (i : Fin n) (r s : Fin (n + 1))
    (hrs : r.val + 1 < s.val ∨ s.val + 1 < r.val) :
    weightedProjectionMatrix w hw s * coordinateSignMatrix i *
      weightedProjectionMatrix w hw r = 0 := by
  simpa only [weightedProjectionMatrix, weightedFourierFlag, coordinateMultiplier,
    signMultiplier, operatorMatrix_toEuclideanCLM, coordinateSignMatrix] using
    weightedFlag_operatorMatrix_tridiagonal w hw
      (EuclideanSpace.basisFun (Cube n) ℂ) i r s hrs

end WeightedCube

end LeanBlast.GotsmanLinial

end

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\BlockVanishing.lean

namespace OAI

/-!
# Vanishing of low antidiagonal blocks

The geometric step is reduced to an explicit finite sum: multiplication on
both sides by the square root of a positive weight turns the weighted pairing
into a Fourier pairing against the signed weight.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace LeanBlast.GotsmanLinial

/-- The threshold convention at zero is compatible with the signed absolute
value identity used to build the weighted grading. -/
theorem abs_mul_thresholdSign (t : ℝ) : |t| * thresholdSign t = t := by
  by_cases ht : 0 ≤ t
  · simp [thresholdSign, ht, abs_of_nonneg ht]
  · simp [thresholdSign, ht, abs_of_neg (lt_of_not_ge ht)]

/-- If the image of one subspace under an operator is orthogonal to a second
subspace, the corresponding projection block vanishes. -/
theorem projectionBlock_eq_zero_of_pairing
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (H : E →L[𝕜] E)
    (hpair : ∀ u ∈ U, ∀ v ∈ V, inner 𝕜 v (H u) = 0) :
    V.starProjection * H * U.starProjection = 0 := by
  ext x
  change V.starProjection (H (U.starProjection x)) = 0
  apply (Submodule.starProjection_apply_eq_zero_iff V).mpr
  intro v hv
  exact hpair _ (U.starProjection_apply_mem x) v hv

/-- Lift an orthogonality calculation on preimages through a common linear map
to a zero block between subspaces of its images. -/
theorem projectionBlock_eq_zero_of_map_pairing
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (A B U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : E →ₗ[𝕜] E) (H : E →L[𝕜] E)
    (hU : U ≤ A.map D) (hV : V ≤ B.map D)
    (hpair : ∀ a ∈ A, ∀ b ∈ B, inner 𝕜 (D b) (H (D a)) = 0) :
    V.starProjection * H * U.starProjection = 0 := by
  apply projectionBlock_eq_zero_of_pairing U V H
  intro u hu v hv
  obtain ⟨a, ha, rfl⟩ := hU hu
  obtain ⟨b, hb, rfl⟩ := hV hv
  exact hpair a ha b hb

/-- The finite pairing identity underlying the low antidiagonal cutoff.
The norm and inner product are the counting Euclidean ones. -/
theorem sqrtWeight_inner_eq_sum
    {Ω : Type*} [Fintype Ω]
    (w h : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (D : EuclideanSpace ℂ Ω →ₗ[ℂ] EuclideanSpace ℂ Ω)
    (hD : ∀ a x, D a x = (Real.sqrt (w x) : ℂ) * a x)
    (H : EuclideanSpace ℂ Ω →L[ℂ] EuclideanSpace ℂ Ω)
    (hH : ∀ a x, H a x = (h x : ℂ) * a x)
    (a b : EuclideanSpace ℂ Ω) :
    inner ℂ (D b) (H (D a)) =
      ∑ x, star (b x) * a x * ((w x : ℂ) * (h x : ℂ)) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [RCLike.inner_apply', hH, hD, hD]
  calc
    star ((Real.sqrt (w x) : ℂ) * b x) *
        ((h x : ℂ) * ((Real.sqrt (w x) : ℂ) * a x)) =
      star (b x) * a x *
        (((Real.sqrt (w x) : ℂ) * (Real.sqrt (w x) : ℂ)) * (h x : ℂ)) := by
          simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
          ring
    _ = star (b x) * a x * ((w x : ℂ) * (h x : ℂ)) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw x)]

/-- Replace the weight times the diagonal sign by the actual signed weight. -/
theorem sqrtWeight_inner_eq_sum_signedWeight
    {Ω : Type*} [Fintype Ω]
    (w h : Ω → ℝ) (q : Ω → ℂ) (hw : ∀ x, 0 ≤ w x)
    (hwq : ∀ x, (w x : ℂ) * (h x : ℂ) = q x)
    (D : EuclideanSpace ℂ Ω →ₗ[ℂ] EuclideanSpace ℂ Ω)
    (hD : ∀ a x, D a x = (Real.sqrt (w x) : ℂ) * a x)
    (H : EuclideanSpace ℂ Ω →L[ℂ] EuclideanSpace ℂ Ω)
    (hH : ∀ a x, H a x = (h x : ℂ) * a x)
    (a b : EuclideanSpace ℂ Ω) :
    inner ℂ (D b) (H (D a)) = ∑ x, star (b x) * a x * q x := by
  rw [sqrtWeight_inner_eq_sum w h hw D hD H hH]
  simp only [hwq]

/-- High Fourier support of the signed weight kills every pairing whose two
unweighted degrees have smaller total degree. -/
theorem sqrtWeight_pairing_eq_zero_of_fourier_separation
    {n r s k : ℕ} (w h : Cube n → ℝ) (q : Cube n → ℂ)
    (hw : ∀ x, 0 ≤ w x) (hwq : ∀ x, (w x : ℂ) * (h x : ℂ) = q x)
    (D : EuclideanSpace ℂ (Cube n) →ₗ[ℂ] EuclideanSpace ℂ (Cube n))
    (hD : ∀ a x, D a x = (Real.sqrt (w x) : ℂ) * a x)
    (H : EuclideanSpace ℂ (Cube n) →L[ℂ] EuclideanSpace ℂ (Cube n))
    (hH : ∀ a x, H a x = (h x : ℂ) * a x)
    (a b : EuclideanSpace ℂ (Cube n))
    (ha : WithLp.ofLp a ∈ fourierSpace n r)
    (hb : WithLp.ofLp b ∈ fourierSpace n s)
    (hq : q ∈ fourierSpaceFrom n k) (hrs : r + s < k) :
    inner ℂ (D b) (H (D a)) = 0 := by
  rw [sqrtWeight_inner_eq_sum_signedWeight w h q hw hwq D hD H hH]
  exact sum_mul_eq_zero_of_fourier_separated (fourierSpace_conj_mul ha hb) hq hrs

/-- The choices `w = |p|` and `h = parity * sign(p)` multiply to the
high-degree signed polynomial, including at a zero of the polynomial. -/
theorem polynomial_signedWeight {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Cube n) :
    ((|polynomialValue p x| : ℝ) : ℂ) *
        ((fullParity x * thresholdSign (polynomialValue p x) : ℝ) : ℂ) =
      walshChar Finset.univ x * (polynomialValue p x : ℂ) := by
  rw [Complex.ofReal_mul]
  calc
    ((|polynomialValue p x| : ℝ) : ℂ) *
        ((fullParity x : ℂ) * (thresholdSign (polynomialValue p x) : ℂ)) =
      (fullParity x : ℂ) *
        (((|polynomialValue p x| : ℝ) : ℂ) *
          (thresholdSign (polynomialValue p x) : ℂ)) := by ring
    _ = walshChar Finset.univ x * (polynomialValue p x : ℂ) := by
      rw [← Complex.ofReal_mul, abs_mul_thresholdSign]
      simp only [fullParity, walshChar, Complex.ofReal_prod]

/-- The weighted pairing vanishes for the polynomial, weight,
and parity-modified threshold sign.  No Fourier-support assumption remains. -/
theorem polynomial_sqrtWeight_pairing_eq_zero
    {n d r s : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0)
    (a b : EuclideanSpace ℂ (Cube n))
    (ha : WithLp.ofLp a ∈ fourierSpace n r)
    (hb : WithLp.ofLp b ∈ fourierSpace n s) (hrs : r + s < n - d) :
    let D := sqrtWeightEquiv (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x))
    inner ℂ (D b)
      (signMultiplier (fun x => fullParity x * thresholdSign (polynomialValue p x)) (D a))
        = 0 := by
  dsimp only
  apply sqrtWeight_pairing_eq_zero_of_fourier_separation
    (fun x => |polynomialValue p x|)
    (fun x => fullParity x * thresholdSign (polynomialValue p x))
    (fun x => walshChar Finset.univ x * (polynomialValue p x : ℂ))
    (fun x => abs_nonneg (polynomialValue p x)) (polynomial_signedWeight p)
    _ (fun a x => sqrtWeightEquiv_apply _ _ a x)
    _ (fun a x => signMultiplier_apply _ a x) a b ha hb
    (parity_polynomialValue_mem_fourierSpaceFrom hp hd) hrs

/-- The operator between two subspaces of weighted low-degree spaces is zero
below the polynomial's degree cutoff. -/
theorem polynomial_projectionBlock_eq_zero
    {n d r s : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0)
    (U V : Submodule ℂ (EuclideanSpace ℂ (Cube n)))
    (hU : U ≤ weightedFourierSpace (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x)) r)
    (hV : V ≤ weightedFourierSpace (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x)) s)
    (hrs : r + s < n - d) :
    V.starProjection *
      signMultiplier (fun x => fullParity x * thresholdSign (polynomialValue p x)) *
        U.starProjection = 0 := by
  apply projectionBlock_eq_zero_of_map_pairing
    (fourierEuclideanSpace n r) (fourierEuclideanSpace n s) U V
    (sqrtWeightEquiv (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x))).toLinearMap _ hU hV
  intro a ha b hb
  apply polynomial_sqrtWeight_pairing_eq_zero (r := r) (s := s) p hp hd hnz a b
  · simpa only [mem_fourierEuclideanSpace] using ha
  · simpa only [mem_fourierEuclideanSpace] using hb
  · exact hrs

/-- Low antidiagonal vanishing for the actual weighted grading constructed
from the polynomial.  All geometric hypotheses are discharged. -/
theorem weightedFlag_block_eq_zero_of_polynomial_degree
    {n d r s : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0) (hrs : r + s < n - d) :
    let K := weightedFourierFlag (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x))
    flagProjection K s *
      signMultiplier (fun x => fullParity x * thresholdSign (polynomialValue p x)) *
        flagProjection K r = 0 := by
  dsimp only
  apply polynomial_projectionBlock_eq_zero (r := r) (s := s) p hp hd hnz
  · simpa only [weightedFourierFlag_succ] using
      flagLayer_le_next
        (weightedFourierFlag (fun x => |polynomialValue p x|)
          (fun x => abs_pos.mpr (hnz x))) r
  · simpa only [weightedFourierFlag_succ] using
      flagLayer_le_next
        (weightedFourierFlag (fun x => |polynomialValue p x|)
          (fun x => abs_pos.mpr (hnz x))) s
  · exact hrs

/-- The same vanishing statement in any orthonormal matrix coordinates, ready
for the Hilbert-Schmidt block coupling. -/
theorem weightedFlag_matrixBlock_eq_zero_of_polynomial_degree
    {n d r s : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0) (hrs : r + s < n - d)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ (Cube n))) :
    let K := weightedFourierFlag (fun x => |polynomialValue p x|)
      (fun x => abs_pos.mpr (hnz x))
    operatorMatrix b (flagProjection K s) *
      operatorMatrix b
        (signMultiplier (fun x => fullParity x * thresholdSign (polynomialValue p x))) *
      operatorMatrix b (flagProjection K r) = 0 := by
  have h := congrArg (operatorMatrix b)
    (weightedFlag_block_eq_zero_of_polynomial_degree p hp hd hnz hrs)
  simpa only [operatorMatrix_mul, operatorMatrix_zero] using h

/-- The concrete cutoff used by the finite block coupling: actual weighted
projection matrices, actual diagonal parity-modified polynomial threshold,
and no unproved construction assumptions. -/
theorem weightedProjectionMatrix_block_eq_zero_of_polynomial_degree
    {n d : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x, polynomialValue p x ≠ 0)
    (r s : Fin (n + 1)) (hrs : r.val + s.val < n - d) :
    let w := fun x => |polynomialValue p x|
    let hw : ∀ x, 0 < w x := fun x => abs_pos.mpr (hnz x)
    weightedProjectionMatrix w hw s *
      signMatrix (fun x => fullParity x * polynomialThreshold p x) *
        weightedProjectionMatrix w hw r = 0 := by
  have h := weightedFlag_matrixBlock_eq_zero_of_polynomial_degree
    (r := r.val) (s := s.val) p hp hd hnz hrs (EuclideanSpace.basisFun (Cube n) ℂ)
  simpa only [weightedProjectionMatrix, flagProjectionMatrix, signMultiplier,
    operatorMatrix_toEuclideanCLM, polynomialThreshold] using h

end LeanBlast.GotsmanLinial

end

end OAI


-- Canonical upstream module: OAI\Combinatorics\GotsmanLinial\Main.lean

namespace OAI

/-!
# Assembly of the Gotsman--Linial average-sensitivity bound

The first lemmas are explicitly conditional assembly bridges. The final
theorems discharge their matrix and counting hypotheses using the concrete
weighted Boolean-cube grading and a sign-preserving constant perturbation.
-/

namespace LeanBlast.GotsmanLinial

open scoped BigOperators

/-- The two analytic constants combine to the constant `8` after
normalizing by the number of cube vertices. This is only a scalar bridge. -/
theorem normalized_edge_bound {N C T a : ℝ} (hN : 0 < N)
    (hedge : C ≤ 2 * T) (henergy : T ≤ 4 * a * N) :
    C / N ≤ 8 * a := by
  apply (div_le_iff₀ hN).mpr
  calc
    C ≤ 2 * T := hedge
    _ ≤ 2 * (4 * a * N) := mul_le_mul_of_nonneg_left henergy (by norm_num)
    _ = 8 * a * N := by ring

/-- Convert a counted-edge identity, edge recovery, and an anticommutator
energy estimate into the desired sensitivity inequality. The counting and energy premises are explicit. -/
theorem sensitivity_bound_of_counting_energy {n d : ℕ}
    (f : Cube n → ℝ) (C T : ℝ)
    (hcount : averageSensitivity f = C / (2 : ℝ) ^ n)
    (hedge : C ≤ 2 * T)
    (henergy : T ≤ 4 * ((d : ℝ) * Real.sqrt (n : ℝ)) * (2 : ℝ) ^ n) :
    averageSensitivity f ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  rw [hcount]
  simpa only [mul_assoc] using
    normalized_edge_bound (pow_pos (by norm_num : (0 : ℝ) < 2) n) hedge henergy

/-- The finite-matrix bound assuming an orthogonal projection family with
binomial multiplicities, coordinate tridiagonality, and low-block vanishing. -/
theorem sensitivity_bound_of_cube_grading {n d : ℕ}
    (f : Cube n → ℝ) (hf : ∀ x, f x = 1 ∨ f x = -1)
    (P : Fin (n + 1) → Matrix (Cube n) (Cube n) ℂ)
    (hP : OrthogonalProjectionFamily P)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (htri : ∀ i : Fin n, BlockTridiagonal P (coordinateSignMatrix i))
    (hvanish : ∀ r s : Fin (n + 1), r.val + s.val < n - d →
      P s * signMatrix (fun x => fullParity x * f x) * P r = 0) :
    averageSensitivity f ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  classical
  let h : Cube n → ℝ := fun x => fullParity x * f x
  let H : Matrix (Cube n) (Cube n) ℂ := signMatrix h
  let M : Matrix (Cube n) (Cube n) ℂ := centeredGrading P
  have hh (x : Cube n) : h x = 1 ∨ h x = -1 := parity_twist_cases hf x
  have htotal : hsNormSq M = (n : ℝ) * (2 : ℝ) ^ n / 4 := by
    change hsNormSq (centeredGrading P) = _
    rw [hsNormSq_centeredGrading_trace hP]
    simp_rw [htrace]
    simpa only [mul_comm] using sum_choose_centered_sq n
  have hcoordinate (i : Fin n) :
      hsNormSq (M * coordinateSignMatrix i - coordinateSignMatrix i * M) ≤ (2 : ℝ) ^ n := by
    simpa only [M, card_cube, Nat.cast_pow, Nat.cast_ofNat] using
      hsNormSq_centeredGrading_commutator_le_card hP (coordinateSignMatrix i)
        (htri i) (coordinateSignMatrix_unitary i)
  have hdistance :
      (∑ x : Cube n, ∑ y : Cube n, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2) ≤ hsNormSq M := by
    rw [htotal]
    exact distance_energy_le_of_coordinate_commutator_bound M hcoordinate
  have hcap (x y : Cube n) (hxy : x ≠ y) : ‖M x y‖ ^ 2 ≤ (1 : ℝ) / 4 := by
    apply off_diagonal_sq_norm_le_quarter_of_commutator_bound M _ x y hxy
    intro i a b
    exact sq_norm_centeredGrading_commutator_entry_le_one hP (coordinateSignMatrix i)
      (htri i) (coordinateSignMatrix_unitary i) a b
  have hedge : ((orderedConstantEdges h).card : ℝ) ≤
      2 * hsNormSq (M * H + H * M) := edge_recovery M h hh htotal hdistance hcap
  have henergy : hsNormSq (M * H + H * M) ≤
      4 * (d : ℝ) * Real.sqrt (n : ℝ) * (2 : ℝ) ^ n :=
    hsNormSq_centeredGrading_anticommutator_le_of_trace n d P hP H
      (signMatrix_conjTranspose_mul h hh) (signMatrix_mul_conjTranspose h hh) htrace hvanish
  apply sensitivity_bound_of_counting_energy f ((orderedConstantEdges h).card : ℝ)
    (hsNormSq (M * H + H * M)) (averageSensitivity_eq_parity_edges hf) hedge
  simpa only [mul_assoc] using henergy

/-- The bound for a polynomial without cube zeros. The projection
family and both block-vanishing properties are constructed from its absolute
value, rather than retained as hypotheses. -/
theorem polynomialThreshold_averageSensitivity_le_of_nonzero {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x : Cube n, polynomialValue p x ≠ 0) :
    averageSensitivity (polynomialThreshold p) ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  let w : Cube n → ℝ := fun x => |polynomialValue p x|
  have hw (x : Cube n) : 0 < w x := abs_pos.mpr (hnz x)
  apply sensitivity_bound_of_cube_grading (polynomialThreshold p)
    (fun x => thresholdSign_cases (polynomialValue p x))
    (weightedProjectionMatrix w hw)
    (weightedProjectionMatrix_family w hw)
    (weightedProjectionMatrix_trace_re w hw)
  · intro i
    exact weightedProjectionMatrix_tridiagonal w hw i
  · intro r s hrs
    exact weightedProjectionMatrix_block_eq_zero_of_polynomial_degree p hp hd hnz r s hrs

/-- Every real multilinear polynomial of degree at most `d` has average
sensitivity at most `8*d*sqrt(n)`, including cube zeros under `sign(0)=1`.
The argument in fact covers all natural `n` and `d`. -/
theorem polynomialThreshold_averageSensitivity_le {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    averageSensitivity (polynomialThreshold p) ≤ 8 * (d : ℝ) * Real.sqrt (n : ℝ) := by
  obtain ⟨q, hq, hqd, hqnz, hqf⟩ := exists_nonzero_polynomial_same_threshold hp hd
  rw [← hqf]
  exact polynomialThreshold_averageSensitivity_le_of_nonzero q hq hqd hqnz

/-- The average-sensitivity bound for `1 ≤ d ≤ n`, without auxiliary
construction hypotheses. -/
theorem gotsmanLinialStatement : GotsmanLinialStatement := by
  intro n d _ _ _ p hp hd
  exact polynomialThreshold_averageSensitivity_le p hp hd

end LeanBlast.GotsmanLinial

end OAI


-- Refinement module: BlockRefinement

open scoped BigOperators
open OAI.LeanBlast.GotsmanLinial
namespace AverageSensitivity

theorem binomial_mad_eq (n : ℕ) :
    (∑ s : Fin (n+1), binomialWeight n s * |(s.val:ℝ)-(n:ℝ)/2|) = mad n := by
  simp only [binomialWeight]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => (n.choose j:ℝ)/(2:ℝ)^n*|(j:ℝ)-(n:ℝ)/2|)]
  unfold mad rawMAD
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  have he : |2*(j:ℝ)-(n:ℝ)| = 2*|(j:ℝ)-(n:ℝ)/2| := by
    rw [show 2*(j:ℝ)-(n:ℝ) = 2*((j:ℝ)-(n:ℝ)/2) by ring,abs_mul]
    norm_num
  rw [he]
  ring

theorem block_coupling_refined
    (n d : ℕ) (B : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hB : ∀ r s, 0 ≤ B r s)
    (hrow : ∀ r, (∑ s : Fin (n + 1), B r s) = (n.choose r.val : ℝ))
    (hcol : ∀ s, (∑ r : Fin (n + 1), B r s) = (n.choose s.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → B r s = 0) :
    (∑ r : Fin (n + 1), ∑ s : Fin (n + 1),
      ((s.val : ℝ) + (r.val : ℝ) - (n : ℝ)) ^ 2 * B r s) ≤
        (4*(d:ℝ)*mad n+(d:ℝ)^2)*(2:ℝ)^n := by
  let w : Fin (n + 1) × Fin (n + 1) → ℝ :=
    normalizedPairWeight B ((2 : ℝ) ^ n)
  let U : Fin (n + 1) × Fin (n + 1) → ℝ := fun t => (t.2.val : ℝ)
  let V : Fin (n + 1) × Fin (n + 1) → ℝ :=
    fun t => (n : ℝ) - (t.1.val : ℝ)
  have hU (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (U t)) =
        ∑ s : Fin (n + 1), binomialWeight n s * φ (s.val : ℝ) := by
    simpa only [w, U, hcol, binomialWeight] using
      normalizedPairWeight_expect_snd B ((2 : ℝ) ^ n)
        (fun s => φ (s.val : ℝ))
  have hV (φ : ℝ → ℝ) :
      (∑ t : Fin (n + 1) × Fin (n + 1), w t * φ (V t)) =
        ∑ r : Fin (n + 1),
          binomialWeight n r * φ ((n : ℝ) - (r.val : ℝ)) := by
    simpa only [w, V, hrow, binomialWeight] using
      normalizedPairWeight_expect_fst B ((2 : ℝ) ^ n)
        (fun r => φ ((n : ℝ) - (r.val : ℝ)))
  have hw : ∀ t, 0 ≤ w t :=
    normalizedPairWeight_nonneg B _ hB (binomialDenominator_pos n).le
  have hprob : (∑ t, w t) = 1 := by
    have h := hU (fun _ => 1)
    simpa only [mul_one, sum_binomialWeight] using h
  have hsame : ∀ φ : ℝ → ℝ,
      (∑ t, w t * φ (U t)) = ∑ t, w t * φ (V t) := by
    intro φ
    rw [hU, hV, binomialWeight_reflect]
  have hstep : ∀ t, w t ≠ 0 → V t - U t ≤ (d : ℝ) := by
    rintro ⟨r, s⟩ ht
    have hnonzero : B r s ≠ 0 := by
      intro hz
      exact ht (by simp only [w, normalizedPairWeight, hz, zero_div])
    have hnat : n - d ≤ r.val + s.val :=
      Nat.le_of_not_gt (fun hlt => hnonzero (hvanish r s hlt))
    have hnat' : n ≤ r.val + s.val + d := by omega
    have hreal : (n : ℝ) ≤ (r.val : ℝ) + (s.val : ℝ) + (d : ℝ) := by
      exact_mod_cast hnat'
    dsimp only [U, V]
    linarith
  have hbound := finite_coupling_refined w U V ((n:ℝ)/2) (d:ℝ)
    hw hprob hsame (Nat.cast_nonneg d) hstep
  have hmad : (∑ t, w t*|U t-(n:ℝ)/2|)=mad n := by
    rw [hU (fun z => |z-(n:ℝ)/2|),binomial_mad_eq]
  rw [hmad] at hbound
  calc
    _ = (2 : ℝ) ^ n * (∑ t, w t * (U t - V t) ^ 2) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [w, U, V, normalizedPairWeight]
      field_simp [binomialDenominator_ne_zero n]
      ring
    _ ≤ (2 : ℝ) ^ n * (4*(d:ℝ)*mad n+(d:ℝ)^2) :=
      mul_le_mul_of_nonneg_left hbound (binomialDenominator_pos n).le
    _ = (4*(d:ℝ)*mad n+(d:ℝ)^2)*(2:ℝ)^n := by ring

/-- The actual finite probability weights supplied by the Hilbert--Schmidt
blocks of an operator in a binomial orthogonal grading. -/
noncomputable def blockCouplingWeight {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin (n + 1) → Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (t : Fin (n + 1) × Fin (n + 1)) : ℝ :=
  normalizedPairWeight (fun r s => hsNormSq (P s * H * P r)) ((2 : ℝ) ^ n) t

theorem blockCouplingWeight_nonneg {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin (n + 1) → Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (t : Fin (n + 1) × Fin (n + 1)) : 0 ≤ blockCouplingWeight P H t :=
  normalizedPairWeight_nonneg _ _ (fun _ _ => hsNormSq_nonneg _)
    (binomialDenominator_pos n).le t

/-- The first block index has the binomial distribution. -/
theorem blockCouplingWeight_fst_marginal {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (H : Matrix ι ι ℂ) (hH : H.conjTranspose * H = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (r : Fin (n + 1)) :
    (∑ s : Fin (n + 1), blockCouplingWeight P H (r, s)) = binomialWeight n r := by
  unfold blockCouplingWeight
  rw [normalizedPairWeight_row, sum_hsNormSq_blocks_column hP H r hH, hmult]
  rfl

/-- The second block index has the same binomial distribution. -/
theorem blockCouplingWeight_snd_marginal {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (H : Matrix ι ι ℂ) (hH : H * H.conjTranspose = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (s : Fin (n + 1)) :
    (∑ r : Fin (n + 1), blockCouplingWeight P H (r, s)) = binomialWeight n s := by
  unfold blockCouplingWeight
  rw [normalizedPairWeight_column, sum_hsNormSq_blocks_row hP H s hH, hmult]
  rfl

/-- Unitarity and the grading multiplicities make the block weights a
probability distribution without any additional normalization assumption. -/
theorem sum_blockCouplingWeight {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {P : Fin (n + 1) → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)
    (H : Matrix ι ι ℂ) (hH : H.conjTranspose * H = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ)) :
    (∑ t : Fin (n + 1) × Fin (n + 1), blockCouplingWeight P H t) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [blockCouplingWeight_fst_marginal hP H hH hmult]
  exact sum_binomialWeight n

/-- A nonzero block probability lies on or above the required anti-diagonal. -/
theorem blockCouplingWeight_support {n d : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin (n + 1) → Matrix ι ι ℂ) (H : Matrix ι ι ℂ)
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0)
    (r s : Fin (n + 1)) (ht : blockCouplingWeight P H (r, s) ≠ 0) :
    n - d ≤ r.val + s.val := by
  apply Nat.le_of_not_gt
  intro hlt
  apply ht
  simp only [blockCouplingWeight, normalizedPairWeight, hvanish r s hlt,
    hsNormSq_zero, zero_div]

/-- The spectral block coupling bounds the actual centered grading
anticommutator.  Its hypotheses are the orthogonal grading, its binomial
multiplicities, unitarity, and the separately proved low-degree vanishing. -/
theorem hsNormSq_centeredGrading_anticommutator_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n d : ℕ) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (hmult : ∀ k, hsNormSq (P k) = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      (4*(d:ℝ)*mad n+(d:ℝ)^2)*(2:ℝ)^n := by
  rw [hsNormSq_centered_anticommutator hP H]
  apply block_coupling_refined n d (fun r s => hsNormSq (P s * H * P r))
  · intro r s
    exact hsNormSq_nonneg _
  · intro r
    rw [sum_hsNormSq_blocks_column hP H r hleft, hmult]
  · intro s
    rw [sum_hsNormSq_blocks_row hP H s hright, hmult]
  · intro r s hrs
    rw [hvanish r s hrs, hsNormSq_zero]

/-- Trace-multiplicity form, for direct use with finite-dimensional orthogonal
projections whose ranks have already been computed. -/
theorem hsNormSq_centeredGrading_anticommutator_le_of_trace {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (n d : ℕ) (P : Fin (n + 1) → Matrix ι ι ℂ)
    (hP : OrthogonalProjectionFamily P) (H : Matrix ι ι ℂ)
    (hleft : H.conjTranspose * H = 1) (hright : H * H.conjTranspose = 1)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (hvanish : ∀ r s, r.val + s.val < n - d → P s * H * P r = 0) :
    hsNormSq (centeredGrading P * H + H * centeredGrading P) ≤
      (4*(d:ℝ)*mad n+(d:ℝ)^2)*(2:ℝ)^n := by
  apply hsNormSq_centeredGrading_anticommutator_le n d P hP H hleft hright _ hvanish
  intro k
  rw [hsNormSq_projection (P k) (hP.conjTranspose_eq k) (hP.idempotent k), htrace]

end AverageSensitivity


-- Refinement module: PolynomialBound

open scoped BigOperators
open OAI.LeanBlast.GotsmanLinial
namespace AverageSensitivity

theorem sensitivity_refined_of_grading {n d : ℕ}
    (f : Cube n → ℝ) (hf : ∀ x, f x = 1 ∨ f x = -1)
    (P : Fin (n + 1) → Matrix (Cube n) (Cube n) ℂ)
    (hP : OrthogonalProjectionFamily P)
    (htrace : ∀ k, (Matrix.trace (P k)).re = (n.choose k.val : ℝ))
    (htri : ∀ i : Fin n, BlockTridiagonal P (coordinateSignMatrix i))
    (hvanish : ∀ r s : Fin (n + 1), r.val + s.val < n - d →
      P s * signMatrix (fun x => fullParity x * f x) * P r = 0) :
    averageSensitivity f ≤ 8*(d:ℝ)*mad n+2*(d:ℝ)^2 := by
  classical
  let h : Cube n → ℝ := fun x => fullParity x * f x
  let H : Matrix (Cube n) (Cube n) ℂ := signMatrix h
  let M : Matrix (Cube n) (Cube n) ℂ := centeredGrading P
  have hh (x : Cube n) : h x = 1 ∨ h x = -1 := parity_twist_cases hf x
  have htotal : hsNormSq M = (n : ℝ) * (2 : ℝ) ^ n / 4 := by
    change hsNormSq (centeredGrading P) = _
    rw [hsNormSq_centeredGrading_trace hP]
    simp_rw [htrace]
    simpa only [mul_comm] using sum_choose_centered_sq n
  have hcoordinate (i : Fin n) :
      hsNormSq (M * coordinateSignMatrix i - coordinateSignMatrix i * M) ≤ (2 : ℝ) ^ n := by
    simpa only [M, card_cube, Nat.cast_pow, Nat.cast_ofNat] using
      hsNormSq_centeredGrading_commutator_le_card hP (coordinateSignMatrix i)
        (htri i) (coordinateSignMatrix_unitary i)
  have hdistance :
      (∑ x : Cube n, ∑ y : Cube n, (hammingDist x y : ℝ) * ‖M x y‖ ^ 2) ≤ hsNormSq M := by
    rw [htotal]
    exact distance_energy_le_of_coordinate_commutator_bound M hcoordinate
  have hcap (x y : Cube n) (hxy : x ≠ y) : ‖M x y‖ ^ 2 ≤ (1 : ℝ) / 4 := by
    apply off_diagonal_sq_norm_le_quarter_of_commutator_bound M _ x y hxy
    intro i a b
    exact sq_norm_centeredGrading_commutator_entry_le_one hP (coordinateSignMatrix i)
      (htri i) (coordinateSignMatrix_unitary i) a b
  have hedge : ((orderedConstantEdges h).card : ℝ) ≤
      2 * hsNormSq (M * H + H * M) := edge_recovery M h hh htotal hdistance hcap
  have henergy : hsNormSq (M * H + H * M) ≤
      (4*(d:ℝ)*mad n+(d:ℝ)^2)*(2:ℝ)^n :=
    hsNormSq_centeredGrading_anticommutator_le_of_trace n d P hP H
      (signMatrix_conjTranspose_mul h hh) (signMatrix_mul_conjTranspose h hh) htrace hvanish
  rw [averageSensitivity_eq_parity_edges hf]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) n)).mpr
  calc
    _ ≤ 2*hsNormSq (M*H+H*M) := hedge
    _ ≤ 2*((4*(d:ℝ)*mad n+(d:ℝ)^2)*(2:ℝ)^n) :=
      mul_le_mul_of_nonneg_left henergy (by norm_num)
    _ = _ := by ring

theorem polynomial_refined_of_nonzero {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d)
    (hnz : ∀ x : Cube n, polynomialValue p x ≠ 0) :
    averageSensitivity (polynomialThreshold p) ≤ 8*(d:ℝ)*mad n+2*(d:ℝ)^2 := by
  let w : Cube n → ℝ := fun x => |polynomialValue p x|
  have hw (x : Cube n) : 0 < w x := abs_pos.mpr (hnz x)
  apply sensitivity_refined_of_grading (polynomialThreshold p)
    (fun x => thresholdSign_cases (polynomialValue p x))
    (weightedProjectionMatrix w hw)
    (weightedProjectionMatrix_family w hw)
    (weightedProjectionMatrix_trace_re w hw)
  · intro i
    exact weightedProjectionMatrix_tridiagonal w hw i
  · intro r s hrs
    exact weightedProjectionMatrix_block_eq_zero_of_polynomial_degree p hp hd hnz r s hrs

theorem polynomial_refined {n d : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hd : p.totalDegree ≤ d) :
    averageSensitivity (polynomialThreshold p) ≤ 8*(d:ℝ)*mad n+2*(d:ℝ)^2 := by
  obtain ⟨q,hq,hqd,hqnz,hqf⟩ := exists_nonzero_polynomial_same_threshold hp hd
  rw [←hqf]
  exact polynomial_refined_of_nonzero q hq hqd hqnz

theorem averageSensitivity_le_dimension {n : ℕ} (f : Cube n → ℝ) :
    averageSensitivity f ≤ (n:ℝ) := by
  classical
  have hcard (i : Fin n) : ((sensitiveVertices f i).card:ℝ) ≤ (2:ℝ)^n := by
    have h : (sensitiveVertices f i).card ≤ Fintype.card (Cube n) := Finset.card_le_univ _
    simpa only [card_cube,Nat.cast_pow,Nat.cast_ofNat] using (Nat.cast_le (α:=ℝ)).mpr h
  calc
    _ ≤ ∑ i : Fin n, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (div_le_one (pow_pos (by norm_num : (0:ℝ)<2) n)).mpr (hcard i)
    _ = _ := by simp

theorem polynomial_bound_3762 {n d : ℕ} (hn : 1≤n) (hd : 1≤d)
    (p : MvPolynomial (Fin n) ℝ) (hp : IsMultilinear p) (hdegree : p.totalDegree≤d) :
    averageSensitivity (polynomialThreshold p) ≤ (1881/500:ℝ)*(d:ℝ)*Real.sqrt (n:ℝ) := by
  exact extract_constant n d hn hd _ (averageSensitivity_le_dimension _) (polynomial_refined p hp hdegree)

end AverageSensitivity


-- Refinement module: Multilinearization

open scoped BigOperators
open OAI.LeanBlast.GotsmanLinial
namespace AverageSensitivity

noncomputable def parityExponent {n : ℕ} (m : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  m.mapRange (fun e => e%2) (by decide)

noncomputable def multilinearize {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ m ∈ p.support, MvPolynomial.monomial (parityExponent m) (MvPolynomial.coeff m p)

theorem multilinearize_isMultilinear {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    IsMultilinear (multilinearize p) := by
  classical
  intro m hm i
  obtain ⟨s,hs,hms⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have he : m=parityExponent s := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hms)
  rw [he]
  simp only [parityExponent,Finsupp.mapRange_apply]
  omega

theorem parityExponent_degree_le {n : ℕ} (m : Fin n →₀ ℕ) :
    (parityExponent m).sum (fun _ e => e) ≤ m.sum (fun _ e => e) := by
  rw [Finsupp.sum_fintype _ _ (by simp),Finsupp.sum_fintype _ _ (by simp)]
  apply Finset.sum_le_sum
  intro i _
  simp only [parityExponent,Finsupp.mapRange_apply]
  exact Nat.mod_le _ _

theorem multilinearize_degree_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    (multilinearize p).totalDegree ≤ p.totalDegree := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans
    ((parityExponent_degree_le m).trans (MvPolynomial.le_totalDegree hm))

theorem sign_pow_mod_two (x : ℝ) (hx : x=1 ∨ x= -1) (e : ℕ) : x^(e%2)=x^e := by
  rcases hx with rfl | rfl
  · simp
  · have he : e=e%2+2*(e/2) := by omega
    conv_rhs => rw [he,pow_add,pow_mul]
    norm_num

theorem multilinearize_value {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Cube n) :
    polynomialValue (multilinearize p) x = polynomialValue p x := by
  classical
  unfold polynomialValue multilinearize
  rw [map_sum]
  conv_rhs => rw [p.as_sum,map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.eval_monomial,MvPolynomial.eval_monomial]
  congr 1
  rw [parityExponent,Finsupp.prod_mapRange_index (by simp)]
  apply Finset.prod_congr rfl
  intro i _
  exact sign_pow_mod_two _ (cubeCoord_cases x i) _

theorem polynomial_bound_3762_general {n d : ℕ} (hn : 1≤n) (hd : 1≤d)
    (p : MvPolynomial (Fin n) ℝ) (hdegree : p.totalDegree≤d) :
    averageSensitivity (polynomialThreshold p) ≤ (1881/500:ℝ)*(d:ℝ)*Real.sqrt (n:ℝ) := by
  have hsame : polynomialThreshold (multilinearize p) = polynomialThreshold p := by
    funext x
    unfold polynomialThreshold
    rw [multilinearize_value]
  rw [←hsame]
  exact polynomial_bound_3762 hn hd _ (multilinearize_isMultilinear p)
    ((multilinearize_degree_le p).trans hdegree)

end AverageSensitivity


theorem solution : type_of% @AverageSensitivity.polynomial_bound_3762_general := @AverageSensitivity.polynomial_bound_3762_general
