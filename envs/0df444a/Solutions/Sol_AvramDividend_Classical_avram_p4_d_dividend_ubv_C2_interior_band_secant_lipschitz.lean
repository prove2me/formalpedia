-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:29:11.863359+00:00
-- url     : https://prove2.me/submissions/b79f9675-471f-482d-8a25-045aea9d1ef5

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- UBV C² source regularity plus an interior derivative envelope yields a
compact reserve-strip secant bound, without any BV standing assumption. -/
theorem solution
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |w s - w t| ≤ (K : ℝ) * |s - t| := by
  have hDiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ w y := by
    intro y hy
    have hd := hwC2.differentiableOn (by norm_num) y (hBand hy)
    exact hd.differentiableAt (hOpen.mem_nhds (hBand hy))
  have hLip : LipschitzOnWith K w (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le hDiff hK
  intro s hs t ht
  simpa only [Real.dist_eq] using hLip.dist_le_mul s hs t ht