-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_uniform_moving_taylor_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:36:18.834796+00:00
-- url     : https://prove2.me/submissions/7944dd0b-dcd0-410a-bf4b-ea71bda83aaa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One finite quadratic Taylor-error envelope applies to every pair of
strict-interior compact-band reserve values. -/
theorem solution
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≠ v →
        |w v - taylorWithinEval w 1 (uIcc u v) u v| ≤
          (K / 2) * (v - u) ^ 2 := by
  have hOpen :
      IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen C
  have hId : iteratedDeriv 2 w = deriv (deriv w) := by
    calc
      iteratedDeriv 2 w = iteratedDeriv (1 + 1) w := by norm_num
      _ = deriv (iteratedDeriv 1 w) := by rw [iteratedDeriv_succ]
      _ = deriv (deriv w) := by rw [iteratedDeriv_one]
  have hCont : ContinuousOn (iteratedDeriv 2 w) (Icc a b) := by
    rw [hId]
    intro y hy
    have hc2 : ContDiffAt ℝ 2 w y :=
      hwC2.contDiffAt (hOpen.mem_nhds (hBand hy))
    have hc1 : ContDiffAt ℝ 1 (deriv w) y :=
      hc2.derivWithin (by norm_num)
    have hc0 : ContDiffAt ℝ 0 (deriv (deriv w)) y :=
      hc1.derivWithin (by norm_num)
    exact hc0.continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hCont
  let K : ℝ := max M 0
  refine ⟨K, le_max_right _ _, ?_⟩
  intro u hu v hv huv
  have hSegment : uIcc u v ⊆ Icc a b :=
    Set.uIcc_subset_Icc hu hv
  have hwSegment : ContDiffOn ℝ (1 + 1) w (uIcc u v) := by
    simpa only [one_add_one_eq_two] using
      (hwC2.mono (hSegment.trans hBand))
  obtain ⟨ξ, hξ, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (n := 1) huv hwSegment
  have hξBand : ξ ∈ Icc a b :=
    hSegment (Set.uIoo_subset_uIcc_self hξ)
  have hBound : |iteratedDeriv 2 w ξ| ≤ K := by
    have hNorm := le_trans (hM ξ hξBand) (le_max_left M 0)
    simpa only [Real.norm_eq_abs] using hNorm
  have hEq :
      w v - taylorWithinEval w 1 (uIcc u v) u v =
        iteratedDeriv 2 w ξ * (v - u) ^ 2 / 2 := by
    norm_num at hTaylor
    simpa using hTaylor
  rw [hEq]
  have hSq : 0 ≤ (v - u) ^ 2 := sq_nonneg _
  calc
    |iteratedDeriv 2 w ξ * (v - u) ^ 2 / 2| =
        |iteratedDeriv 2 w ξ| * ((v - u) ^ 2 / 2) := by
          rw [abs_div, abs_mul, abs_of_nonneg hSq]
          norm_num
          ring
    _ ≤ K * ((v - u) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hBound
        (div_nonneg hSq (by norm_num))
    _ = (K / 2) * (v - u) ^ 2 := by ring
