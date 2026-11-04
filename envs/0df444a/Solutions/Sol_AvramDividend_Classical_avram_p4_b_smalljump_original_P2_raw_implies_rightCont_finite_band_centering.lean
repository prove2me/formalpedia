-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_P2_raw_implies_rightCont_finite_band_centering
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:36:16.57333+00:00
-- url     : https://prove2.me/submissions/9a5c22d0-4aad-43f1-9617-36c2ee6ddf62

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_raw_compensator_to_rightCont_event_rate
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_band_event_rate_implies_real_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Finite original marked jumps have a centred real-valued increment on the
right-continuous source filtration, assuming the genuine P2 raw compensator
and its unconditional physical mark rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ a b ω, J a b ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc a b ×ˢ B))
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (hFinite : X.ν B ≠ ⊤)
    (hMass : ∀ C : Set Ω, MeasurableSet[𝓕.rightCont s] C → P C ≠ ⊤)
    (hRate : ∀ n, (∫⁻ ω, J s (r n) ω ∂P) =
      ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (hRaw : ∀ (u v : ℝ≥0) (C : Set Ω), u ≤ v →
      MeasurableSet[𝓕 u] C →
      (∫⁻ ω in C, J u v ω ∂P) =
        P C * ((v - u : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (hJmeas : Measurable (J s t))
    (hFullRate : (∫⁻ ω, J s t ω ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    P[(fun ω => (J s t ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) |
      𝓕.rightCont s] =ᵐ[P] 0 := by
  have hRateRight (C : Set Ω) (hC : MeasurableSet[𝓕.rightCont s] C) :
      (∫⁻ ω in C, J s t ω ∂P) =
        P C * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
    simpa only [mul_assoc] using
      (avram_p4_b_smalljump_original_raw_compensator_to_rightCont_event_rate
        X s t r hsr hrt B hB C hC J hJsource hShort hLong
        hFinite (hMass C hC) hRate hRaw)
  have hMoment :=
    avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite
      X s t B (J s t) (hJsource s t) hJmeas hFullRate hFinite
  exact avram_p4_b_smalljump_original_finite_band_event_rate_implies_real_condExp_zero
    X s t B (J s t) (hJsource s t) hJmeas hMoment.2 hMoment.1
    (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) hRateRight
