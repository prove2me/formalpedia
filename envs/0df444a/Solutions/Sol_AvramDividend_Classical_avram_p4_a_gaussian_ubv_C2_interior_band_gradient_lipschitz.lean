-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_interior_band_gradient_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:39:18.267623+00:00
-- url     : https://prove2.me/submissions/aced65c6-8db1-48ec-a882-1cde453c3942

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Strict-interior C² gives a compact-band Lipschitz envelope on the first
derivative, with no global regularity or boundary extension assumptions. -/
theorem solution
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc a b, ‖deriv (deriv w) y‖₊ ≤ K) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |deriv w s - deriv w t| ≤ (K : ℝ) * |s - t| := by
  have hDiff : ∀ y ∈ Icc a b,
      DifferentiableAt ℝ (deriv w) y := by
    intro y hy
    have hc2 : ContDiffAt ℝ 2 w y :=
      hwC2.contDiffAt (hOpen.mem_nhds (hBand hy))
    have hc1 : ContDiffAt ℝ 1 (deriv w) y :=
      hc2.derivWithin (by norm_num)
    exact hc1.differentiableAt (by norm_num)
  have hLip : LipschitzOnWith K (deriv w) (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le hDiff hK
  intro s hs t ht
  simpa only [Real.dist_eq] using hLip.dist_le_mul s hs t ht
