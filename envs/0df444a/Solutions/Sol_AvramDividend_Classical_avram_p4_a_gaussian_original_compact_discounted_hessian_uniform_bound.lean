-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_compact_discounted_hessian_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:43:04.07041+00:00
-- url     : https://prove2.me/submissions/feccc5e5-b71b-4371-8f2b-be80b3775312

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual Levy Gaussian coefficient has a uniformly bounded
 discounted Hessian on every compact strict interior band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (t : ℝ≥0) (y : ℝ), y ∈ Icc a b →
        |Real.exp (-(q * (t : ℝ))) *
          (X.σ ^ 2 / 2 * iteratedDeriv 2 w y)| ≤ K := by
  have hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
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
  let B : ℝ := max M 0
  let S : ℝ := |X.σ ^ 2 / 2|
  let K : ℝ := S * B
  have hB : 0 ≤ B := le_max_right M 0
  have hS : 0 ≤ S := abs_nonneg _
  refine ⟨K, mul_nonneg hS hB, ?_⟩
  intro t y hy
  have hSecond : |iteratedDeriv 2 w y| ≤ B := by
    have hNorm := le_trans (hM y hy) (le_max_left M 0)
    simpa only [Real.norm_eq_abs] using hNorm
  have hExpNonneg : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  have hExpLe : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have ht : (0 : ℝ) ≤ (t : ℝ) := NNReal.coe_nonneg t
    exact neg_nonpos.mpr (mul_nonneg hq ht)
  calc
    |Real.exp (-(q * (t : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w y)| =
      Real.exp (-(q * (t : ℝ))) * (S * |iteratedDeriv 2 w y|) := by
        simp [S, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-(q * (t : ℝ))) * (S * B) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hSecond hS) hExpNonneg
    _ ≤ K := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hExpLe (mul_nonneg hS hB))
