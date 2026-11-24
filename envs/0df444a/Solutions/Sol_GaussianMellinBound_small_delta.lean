-- Prove2me | solution 1 for GaussianMellinBound.small_delta
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T03:40:28.877226+00:00
-- url     : https://prove2.me/submissions/9bb2ae34-6adb-4235-88f6-70a540eba130

import Mathlib.Analysis.MellinTransform
import Theorems.Thm_GaussianMellinBound_small_delta_p1
import Theorems.Thm_GaussianMellinBound_small_delta_p2
import Theorems.Thm_GaussianMellinBound_small_delta_p3
import Theorems.Thm_GaussianMellinBound_small_delta_p4

open Real

theorem solution (δ : ℝ) (hδ : |δ| ≤ 1) {t : ℝ}
    (hlo : -(23 / 16) ≤ t) (hhi : t ≤ -1) :
    ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
      ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ ≤
      (3 / 2) * ‖mellin (fun u : ℝ => (Real.exp (-u ^ 2 / 2) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((δ * u : ℝ) : ℂ)))
        ((1 / 2 : ℂ) - Complex.I)‖ := by
  have hd := abs_le.mp hδ
  rcases le_total δ (-(3 / 4)) with h1 | h1
  · exact GaussianMellinBound.small_delta_p1 δ hd.1 h1 hlo hhi
  · rcases le_total δ (-(1 / 2)) with h2 | h2
    · exact GaussianMellinBound.small_delta_p2 δ h1 h2 hlo hhi
    · rcases le_total δ 0 with h3 | h3
      · exact GaussianMellinBound.small_delta_p3 δ h2 h3 hlo hhi
      · exact GaussianMellinBound.small_delta_p4 δ h3 hd.2 hlo hhi
