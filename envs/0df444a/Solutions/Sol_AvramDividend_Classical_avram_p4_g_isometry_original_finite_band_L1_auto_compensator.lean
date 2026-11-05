-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_finite_band_L1_auto_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:47:48.549201+00:00
-- url     : https://prove2.me/submissions/67206248-4c5a-4b67-bad7-376ffee26035

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_band_count_L1_of_rectangle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original P2-E intrinsic rectangle law yields integrability and finite count on every strict finite negative band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : X.ν B < ⊤)
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)) :
    Integrable (fun ω => (N ω).toReal) P ∧
      (∀ᵐ ω ∂P, N ω < ⊤) := by
  have hMeas : Measurable N := by
    rw [hActual]
    exact avram_p2_e_compensator_original_intrinsic_marked_count_measurable
      X s t hst B hB
  have hRect : ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫⁻ ω in A, N ω ∂P) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    intro A hA
    rw [hActual]
    exact avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
      X s t hst A hA B hB
  exact avram_p4_g_isometry_original_finite_band_count_L1_of_rectangle
    X s t hst ε hε B hB hBand hν N hActual hMeas hRect
