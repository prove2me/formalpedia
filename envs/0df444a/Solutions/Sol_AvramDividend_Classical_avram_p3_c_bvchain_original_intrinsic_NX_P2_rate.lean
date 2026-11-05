-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_intrinsic_NX_P2_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:54:01.480756+00:00
-- url     : https://prove2.me/submissions/190b2ccb-f956-4890-b1a6-24f9e8206191

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine original X intrinsic marked measure obeys the now-Proved P2 rectangle
compensator rate with no new source-rate assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) :
    ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω in A, NX ω (Ioc s t ×ˢ B) ∂P) =
          P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  intro s t hst A hA B hB
  have hP2 :=
    avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
      X s t hst A hA B hB
  simpa only [hNX] using hP2
