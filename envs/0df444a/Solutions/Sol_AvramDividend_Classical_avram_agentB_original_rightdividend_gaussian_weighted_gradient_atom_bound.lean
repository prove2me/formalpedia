-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_original_rightdividend_gaussian_weighted_gradient_atom_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:23:36.212274+00:00
-- url     : https://prove2.me/submissions/6cce81c5-1a96-4369-b9ab-3bdb63ba9c28

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger23_original_samegrid_prepost_gradient_jump_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

/-- Genuine right-dividend gradient atom error on a compact C² band
obeys the original exact mass-weighted Gaussian grid estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv (deriv w) y‖₊ ≤ K)
    (s : ℝ≥0) (ω : Ω)
    (hPre : riskProcess X x D s ω ∈ Icc a b)
    (hPost : x + X.X s ω - rightLimit D s ω ∈ Icc a b)
    (hRight : 0 ≤ rightLimit D s ω - D s ω)
    (e z : ℝ) (he : 0 ≤ e) :
    e * |deriv w (x + X.X s ω - rightLimit D s ω) -
           deriv w (riskProcess X x D s ω)| * |z| ≤
       e * ((K : ℝ) * (rightLimit D s ω - D s ω)) * |z| := by
  have h := avram_gledger23_original_samegrid_prepost_gradient_jump_bound
    X x D C w hw a b hOpen hBand K hK s ω hPre hPost hRight
  have hswap :
      |deriv w (x + X.X s ω - rightLimit D s ω) -
        deriv w (riskProcess X x D s ω)| ≤
        (K : ℝ) * (rightLimit D s ω - D s ω) := by
    simpa only [abs_sub_comm] using h
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hswap he) (abs_nonneg z)
