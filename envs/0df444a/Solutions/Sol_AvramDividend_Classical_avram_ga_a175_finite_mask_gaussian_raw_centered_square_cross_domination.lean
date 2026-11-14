-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a175_finite_mask_gaussian_raw_centered_square_cross_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:51:12.02292+00:00
-- url     : https://prove2.me/submissions/44b44d2b-2b97-4d35-8d0d-1e48698fff16

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a85_gaussian_raw_centered_square_triangle
import Theorems.Thm_AvramDividend_Classical_avram_ga_a84_centered_gaussian_quadratic_cross_young_product
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- Exact physical finite-mask raw-centred quadratic energy bound, pointwise. -/
theorem solution
    {Ω : Type*} (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (Z : ℕ → Ω → ℝ) (d : ℝ) (ω : Ω) :
    (∑ i ∈ S, if A i ω then
      |(Z i ω + d)^2 - (Z i ω)^2| else 0) ≤
    (∑ i ∈ S, if A i ω then (Z i ω)^2 else 0) +
      (S.card : ℝ) * (2 * d^2) := by
  classical
  calc
    (∑ i ∈ S, if A i ω then
      |(Z i ω + d)^2 - (Z i ω)^2| else 0) ≤
      ∑ i ∈ S, ((if A i ω then (Z i ω)^2 else 0) + 2 * d^2) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases h : A i ω
        · simp only [if_pos h]
          have h1 := avram_ga_a85_gaussian_raw_centered_square_triangle (Z i ω) d
          have h2 := avram_ga_a84_centered_gaussian_quadratic_cross_young_product
            (Z i ω) d 1 (by norm_num)
          norm_num at h2
          linarith
        · simp only [if_neg h]
          positivity
    _ = (∑ i ∈ S, if A i ω then (Z i ω)^2 else 0) +
        (S.card : ℝ) * (2 * d^2) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
