-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.child_invariants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:54:47.340527+00:00
-- url     : https://prove2.me/submissions/571dd252-4f35-4d8d-9726-aa6fe5d9a67b

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
import Theorems.Thm_FD1D_V5_LocalPolicy_parent_interval_bound
import Theorems.Thm_FD1D_V5_LocalPolicy_bias_nonneg_of_ordered
import Theorems.Thm_FD1D_V5_LocalPolicy_orderedBias_le_uniform
import Theorems.Thm_FD1D_V5_LocalPolicy_massLeft_eq_count_mul_rateLeft
import Theorems.Thm_FD1D_V5_LocalPolicy_massRight_eq_count_mul_rateRight
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_V5_LocalPolicy_inventory_nonneg
import Theorems.Thm_FD1D_V5_LocalPolicy_parentMass_swap
import Theorems.Thm_FD1D_V5_LocalPolicy_rateLeft_swap
import Theorems.Thm_FD1D_V5_LocalPolicy_rateRight_swap
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


section
namespace FD1D.V5.LocalPolicy
noncomputable section
private theorem orderedBias_eq_caps
    {a p h : ℝ} {x y : ℕ}
    (hxy : y < x) (hy : 0 < y) :
    orderedBias a p h x y =
      min (feedbackCandidate a h x y)
        (min (uniformCandidate h x y) (floorCandidate a p h x y)) := by
  unfold orderedBias
  rw [if_neg (by omega : x ≠ y)]
  rw [if_neg (by omega : x + y ≠ 0)]
  rw [if_neg (by omega : y ≠ 0)]
private theorem floorCandidate_pos
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hxy : y ≤ x) (hy : 0 < y)
    (ht : discrepancy a p h x y ≤ h / 2) :
    0 < floorCandidate a p h x y := by
  have hx : 0 < (x : ℝ) := by exact_mod_cast lt_of_lt_of_le hy hxy
  have hy' : 0 < (y : ℝ) := by exact_mod_cast hy
  have hden : 0 < 2 * (y : ℝ) + a := by positivity
  have hp := parent_interval_bound ha ht
  unfold floorCandidate parentMass inventory at *
  apply sub_pos.mpr
  apply (div_lt_iff₀ hden).2
  nlinarith [mul_pos ha (mul_pos hh hx)]
private theorem child_regularized_le_rate
    {a p q : ℝ} {n : ℕ}
    (ha : 0 < a) (hn : 0 < n)
    (hmass : p * (n : ℝ) ≤ q * (2 * (n : ℝ) + a)) :
    (p / 2) / ((n : ℝ) + a / 2) ≤ q / n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < 2 * (n : ℝ) + a := by positivity
  have heq : (p / 2) / ((n : ℝ) + a / 2) =
      p / (2 * (n : ℝ) + a) := by
    field_simp
  rw [heq]
  exact (div_le_div_iff₀ hden hn').2 hmass
private theorem ordered_child_invariants
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (hxy : y ≤ x)
    (ht : discrepancy a p h x y ≤ h / 2) :
    regularizedMassLeft a p x y ≤ rateLeft a p h x y ∧
      regularizedMassRight a p x y ≤ rateRight a p h x y := by
  by_cases hy : y = 0
  · subst y
    by_cases hx0 : x = 0
    · subst x
      have ht' : p / a ≤ h / 2 := by
        simpa [discrepancy, parentMass, inventory] using ht
      have heq : p / 2 / (a / 2) = p / a := by
        field_simp
      constructor <;>
        simp [regularizedMassLeft, regularizedMassRight, rateLeft,
          rateRight, heq] <;>
        linarith
    have hx : 0 < x := Nat.pos_of_ne_zero hx0
    have hsum : x + 0 ≠ 0 := by omega
    have hb : bias a p h x 0 = parentMass h x 0 := by
      simp [bias, orderedBias, hxy, hx.ne']
    have hML : massLeft a p h x 0 = parentMass h x 0 := by
      simp [massLeft, hb]
    have hMR : massRight a p h x 0 = 0 := by
      simp [massRight, hb]
    constructor
    · rw [rateLeft, if_neg hsum, if_neg (by omega : x ≠ 0), hML]
      apply child_regularized_le_rate ha hx
      have hpbound := parent_interval_bound ha ht
      unfold parentMass inventory at *
      nlinarith [mul_nonneg hp.le (Nat.cast_nonneg x)]
    · rw [rateRight, if_neg hsum, if_pos rfl]
      unfold regularizedMassRight
      have heq : (p / 2) / ((0 : ℝ) + a / 2) = p / a := by
        field_simp
        ring
      norm_num only [Nat.cast_zero, zero_add] at *
      rw [heq]
      exact le_max_right _ _
  · have hypos : 0 < y := Nat.pos_of_ne_zero hy
    have hxpos : 0 < x := lt_of_lt_of_le hypos hxy
    have hsum : x + y ≠ 0 := by omega
    have hb0 := bias_nonneg_of_ordered ha hh hxy ht
    have hbU : bias a p h x y ≤ uniformCandidate h x y := by
      rw [bias, if_pos hxy]
      exact orderedBias_le_uniform hxy hypos
    have hbF : bias a p h x y ≤ floorCandidate a p h x y := by
      rw [bias, if_pos hxy]
      by_cases heq : x = y
      · subst x
        simpa [orderedBias] using
          (floorCandidate_pos ha hh (le_refl y) hypos ht).le
      · rw [orderedBias_eq_caps (lt_of_le_of_ne hxy (Ne.symm heq)) hypos]
        exact (min_le_right _ _).trans (min_le_right _ _)
    have hq0 : 0 ≤ parentMass h x y := by
      exact mul_nonneg (inventory_nonneg x y) hh.le
    have hMLhalf : parentMass h x y / 2 ≤ massLeft a p h x y := by
      unfold massLeft
      nlinarith
    have hMRfloor :
        p * (y : ℝ) ≤
          massRight a p h x y * (2 * (y : ℝ) + a) := by
      unfold floorCandidate at hbF
      unfold massRight
      have hden : 0 < 2 * (y : ℝ) + a := by positivity
      have hmul := (div_le_iff₀ hden).1 (show
        2 * p * (y : ℝ) / (2 * (y : ℝ) + a) ≤
          parentMass h x y - bias a p h x y by linarith)
      nlinarith
    have hMLfloor :
        p * (x : ℝ) ≤
          massLeft a p h x y * (2 * (x : ℝ) + a) := by
      have hpbound := parent_interval_bound ha ht
      have hfactor : 0 ≤ 2 * (x : ℝ) + a := by positivity
      have hx' : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
      have hy' : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
      have hpMul := mul_le_mul_of_nonneg_right hpbound hx'
      have hmassMul := mul_le_mul_of_nonneg_right hMLhalf hfactor
      unfold parentMass inventory at hpMul hmassMul
      nlinarith [mul_nonneg hh.le hy']
    constructor
    · rw [rateLeft, if_neg hsum, if_neg (by omega : x ≠ 0)]
      exact child_regularized_le_rate ha hxpos hMLfloor
    · rw [rateRight, if_neg hsum, if_neg hy]
      exact child_regularized_le_rate ha hypos hMRfloor
private theorem discrepancyLeft_le_half_of_regularized
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a)
    (hZ : regularizedMassLeft a p x y ≤ rateLeft a p h x y) :
    discrepancyLeft a p h x y ≤ rateLeft a p h x y / 2 := by
  have hden : 0 < (x : ℝ) + a / 2 := by positivity
  have hmul := (div_le_iff₀ hden).1 hZ
  unfold regularizedMassLeft at hmul
  unfold discrepancyLeft
  apply (div_le_iff₀ ha).2
  rw [massLeft_eq_count_mul_rateLeft]
  nlinarith
private theorem discrepancyRight_le_half_of_regularized
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a)
    (hZ : regularizedMassRight a p x y ≤ rateRight a p h x y) :
    discrepancyRight a p h x y ≤ rateRight a p h x y / 2 := by
  have hden : 0 < (y : ℝ) + a / 2 := by positivity
  have hmul := (div_le_iff₀ hden).1 hZ
  unfold regularizedMassRight at hmul
  unfold discrepancyRight
  apply (div_le_iff₀ ha).2
  rw [massRight_eq_count_mul_rateRight]
  nlinarith
end
end FD1D.V5.LocalPolicy
end

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (ht : discrepancy a p h x y ≤ h / 2) :
    discrepancyLeft a p h x y ≤ rateLeft a p h x y / 2 ∧
      regularizedMassLeft a p x y ≤ rateLeft a p h x y ∧
      discrepancyRight a p h x y ≤ rateRight a p h x y / 2 ∧
      regularizedMassRight a p x y ≤ rateRight a p h x y := by
  have hZ :
      regularizedMassLeft a p x y ≤ rateLeft a p h x y ∧
        regularizedMassRight a p x y ≤ rateRight a p h x y := by
    by_cases hxy : y ≤ x
    · exact ordered_child_invariants ha hp hh hxy ht
    · have hyx : x ≤ y := Nat.le_of_not_ge hxy
      have htSwap :
          discrepancy a p h y x ≤ h / 2 := by
        simpa [discrepancy, parentMass_swap] using ht
      have hs := ordered_child_invariants ha hp hh hyx htSwap
      constructor
      · calc
          regularizedMassLeft a p x y =
              regularizedMassRight a p y x := by
                rfl
          _ ≤ rateRight a p h y x := hs.2
          _ = rateLeft a p h x y := rateRight_swap a p h x y
      · calc
          regularizedMassRight a p x y =
              regularizedMassLeft a p y x := by
                rfl
          _ ≤ rateLeft a p h y x := hs.1
          _ = rateRight a p h x y := rateLeft_swap a p h x y
  have htL :
      discrepancyLeft a p h x y ≤ rateLeft a p h x y / 2 :=
    discrepancyLeft_le_half_of_regularized ha hZ.1
  have htR :
      discrepancyRight a p h x y ≤ rateRight a p h x y / 2 :=
    discrepancyRight_le_half_of_regularized ha hZ.2
  exact ⟨htL, hZ.1, htR, hZ.2⟩
end FD1D.V5.LocalPolicy
