-- Prove2me | solution 1 for Formalism.DivisionValues.divisor_bounds_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:27.9918+00:00
-- url     : https://prove2.me/submissions/e8d2bcb2-4179-49ce-8b48-4f333b724c08

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementACE
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : BoundsSum := by
  intro Pl J _ S D hD lcvR logκ LG E3 lcvM L E1 E2 l ell vG g I Ic jT F err Jx η hl h0 hvG hLG hL
    hI hjT hE1 hE2 hE3
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : ∑ j, lcvM j ≤ (D : ℝ) * ∑ j, L j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      have := (div_le_iff₀ hDr).1 (hL j)
      linarith
  have h2 : ∑ w ∈ S, l w * vG w ≤ (D : ℝ) * LG := by
    calc ∑ w ∈ S, l w * vG w ≤ ∑ w ∈ S, (D : ℝ) * (l w * g w) :=
          Finset.sum_le_sum fun w hw => by
            have := mul_le_mul_of_nonneg_left (hvG w hw) (hl w)
            linarith
      _ = (D : ℝ) * ∑ w ∈ S, l w * g w := by rw [Finset.mul_sum]
      _ ≤ (D : ℝ) * LG := mul_le_mul_of_nonneg_left hLG hDr.le
  have f1 : ∑ w ∈ S, l w * (vG w + ∑ j, (I w j + Ic w j + jT w j)) =
      ∑ w ∈ S, l w * vG w + ∑ w ∈ S, l w * ∑ j, (I w j + Ic w j) +
        ∑ w ∈ S, l w * ∑ j, jT w j := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_add_distrib]
    ring
  have f4 : ∑ w ∈ S, l w * ∑ j, (I w j + Ic w j) ≤
      (D : ℝ) * 2 * ∑ w ∈ S, l w * ∑ j, F w j + (D : ℝ) * ∑ w ∈ S, l w * ∑ j, err w j +
        (D : ℝ) * ∑ w ∈ S, l w * (2 / ell w ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w hw => ?_
    have h := mul_le_mul_of_nonneg_left (hI w hw) (hl w)
    have e : ∑ j, (2 * F w j + err w j) = 2 * ∑ j, F w j + ∑ j, err w j := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [e] at h
    linarith
  have f6 : ∑ w ∈ S, l w * ∑ j, jT w j ≤
      (D : ℝ) * ∑ w ∈ S, l w * ∑ j, Jx w j + ∑ w ∈ S, l w * ∑ j, η w j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w hw => ?_
    have h : ∑ j, jT w j ≤ (D : ℝ) * ∑ j, Jx w j + ∑ j, η w j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => by have := hjT w hw j; linarith
    have := mul_le_mul_of_nonneg_left h (hl w)
    linarith
  have eswap : ∀ f : Pl → J → ℝ, ∑ j, ∑ w ∈ S, l w * f w j = ∑ w ∈ S, l w * ∑ j, f w j := by
    intro f
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  have f8 : ∑ w ∈ S, l w * ∑ j, err w j + ∑ w ∈ S, l w * ∑ j, Jx w j ≤ ∑ j, E1 j := by
    rw [← eswap, ← eswap, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => by
      refine le_trans (le_of_eq ?_) (hE1 j)
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
  have f9 : ∑ w ∈ S, l w * ∑ j, η w j ≤ (D : ℝ) * ∑ j, E2 j := by
    rw [← eswap, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      have h := hE2 j
      rw [← Finset.sum_div] at h
      have := (div_le_iff₀ hDr).1 h
      linarith
  have f10 : (D : ℝ) * ∑ w ∈ S, l w * (2 / ell w ^ 2) ≤ (D : ℝ) * E3 :=
    mul_le_mul_of_nonneg_left hE3 hDr.le
  have f11 : ∑ j, (E1 j + E2 j) = ∑ j, E1 j + ∑ j, E2 j := Finset.sum_add_distrib
  have eF := eswap F
  rw [div_le_iff₀ hDr]
  have hD0 : (0 : ℝ) ≤ D := hDr.le
  nlinarith [h0, h1, h2, f1, f4, f6, f8, f9, f10, f11, eF, mul_le_mul_of_nonneg_left f8 hD0]
end Formalism.DivisionValues
