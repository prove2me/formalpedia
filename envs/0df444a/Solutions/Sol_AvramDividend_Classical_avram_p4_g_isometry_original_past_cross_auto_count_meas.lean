-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_past_cross_auto_count_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:55:37.13172+00:00
-- url     : https://prove2.me/submissions/b7ae76f6-9b0e-410c-a0ab-2959f3837171

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_past_cross_zero_from_proved_compensator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Physical original-process past products are orthogonal to future compensated counts with count measurability derived from P2-E. -/
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
  letI : MeasurableSpace Ω := mΩ
  have hNMeas : Measurable N := by
    rw [hActual]
    exact avram_p2_e_compensator_intrinsic_rectangle_count_measurable
      X s t hst B hB
  exact avram_p4_g_isometry_original_past_cross_zero_from_proved_compensator
    X s t hst ε hε B hB hBand hν N hActual hNMeas
    U V hU hV hUVL2 hCountL2
