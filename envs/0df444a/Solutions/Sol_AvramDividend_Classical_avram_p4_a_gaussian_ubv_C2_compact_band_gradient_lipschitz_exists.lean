-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ubv_C2_compact_band_gradient_lipschitz_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:54:47.023679+00:00
-- url     : https://prove2.me/submissions/2ec72e76-28c6-49c4-8b2e-4414ad47acc0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact strict-interior C² hypothesis automatically supplies a
finite compact-band Lipschitz constant for the first derivative. -/
theorem solution
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ≥0, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |deriv w s - deriv w t| ≤ (K : ℝ) * |s - t| := by
  have hCont : ContinuousOn (deriv (deriv w)) (Icc a b) := by
    intro y hy
    have hc2 : ContDiffAt ℝ 2 w y :=
      hwC2.contDiffAt (hOpen.mem_nhds (hBand hy))
    have hc1 : ContDiffAt ℝ 1 (deriv w) y :=
      hc2.derivWithin (by norm_num)
    have hc0 : ContDiffAt ℝ 0 (deriv (deriv w)) y :=
      hc1.derivWithin (by norm_num)
    exact hc0.continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hCont
  let K : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hK : ∀ y ∈ Icc a b, ‖deriv (deriv w) y‖₊ ≤ K := by
    intro y hy
    apply NNReal.coe_le_coe.mp
    change ‖deriv (deriv w) y‖ ≤ max M 0
    exact le_trans (hM y hy) (le_max_left M 0)
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
  refine ⟨K, ?_⟩
  intro s hs t ht
  simpa only [Real.dist_eq] using hLip.dist_le_mul s hs t ht
