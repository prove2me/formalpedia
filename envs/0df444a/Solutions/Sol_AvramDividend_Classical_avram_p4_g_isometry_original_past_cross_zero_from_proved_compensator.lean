-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_past_cross_zero_from_proved_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:32:18.848197+00:00
-- url     : https://prove2.me/submissions/315bddef-b8ee-4e54-a691-376bb36bd646

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_band_weighted_L2_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Original intrinsic finite-band compensated count is orthogonal to two past coefficients with an L² product. -/
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
        (Ioc s t ×ˢ B))
    (hMeas : Measurable N)
    (U V : Ω → ℝ)
    (hU : StronglyMeasurable[𝓕 s] U)
    (hV : StronglyMeasurable[𝓕 s] V)
    (hUVL2 : MemLp (fun ω => U ω * V ω) 2 P)
    (hCountL2 : MemLp (fun ω =>
      (N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P) :
    (∫ ω, U ω * (V ω *
      ((N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) ∂P) = 0 := by
  have hRect : ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫⁻ ω in A, N ω ∂P) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    intro A hA
    simpa only [hActual] using
      (avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
        X s t hst A hA B hB)
  have hUV : StronglyMeasurable[𝓕 s]
      (fun ω => U ω * V ω) := hU.mul hV
  have hZero := avram_p4_g_isometry_original_finite_band_weighted_L2_zero
    X s t hst ε hε B hB hBand hν N hActual hMeas hRect
    (fun ω => U ω * V ω) hUV hUVL2 hCountL2
  simpa only [mul_assoc] using hZero
