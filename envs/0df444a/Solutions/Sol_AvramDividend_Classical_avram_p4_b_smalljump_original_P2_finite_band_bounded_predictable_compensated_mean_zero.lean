-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_P2_finite_band_bounded_predictable_compensated_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:42:07.397058+00:00
-- url     : https://prove2.me/submissions/ea978425-6a02-40da-bded-58e62858fe77

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_raw_implies_rightCont_finite_band_centering
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_bounded_predictable_weight_count_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_weight_condExp_zero_implies_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original Lévy finite-band compensated random predictable step has
mean zero on the original source probability space, conditional on the true
P2 raw jump compensator and physical first-moment rates. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
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
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (H : Ω → ℝ) (C : ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (hBound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ C) :
    (∫ ω, H ω * ((J s t ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ∂P) = 0 := by
  let rate : ℝ≥0∞ := ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B
  have hMoment :=
    avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite
      X s t B (J s t) (hJsource s t) hJmeas hFullRate hFinite
  have hYint : Integrable (fun ω => (J s t ω).toReal - rate.toReal) P :=
    hMoment.1.sub (integrable_const rate.toReal)
  have hYcenter :=
    avram_p4_b_smalljump_original_P2_raw_implies_rightCont_finite_band_centering
      X s t r hsr hrt B hB J hJsource hShort hLong hFinite
      hMass hRate hRaw hJmeas hFullRate
  have hWeightedCenter :=
    avram_p4_b_smalljump_original_bounded_predictable_weight_count_condExp_zero
      X s t B (J s t) (hJsource s t) rate hYint hYcenter
      H C hH hBound
  have hHm : StronglyMeasurable H :=
    hH.mono ((𝓕.rightCont).le s)
  have hWeightedInt : Integrable (fun ω =>
      H ω * ((J s t ω).toReal - rate.toReal)) P :=
    Integrable.bdd_mul hYint hHm.aestronglyMeasurable hBound
  exact avram_p4_b_smalljump_original_predictable_weight_condExp_zero_implies_mean_zero
    X s t B (J s t) (hJsource s t) rate H hWeightedInt hWeightedCenter
