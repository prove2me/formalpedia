-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_signed_past_weighted_real_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:40:33.997424+00:00
-- url     : https://prove2.me/submissions/0c67db87-ccaa-4bc2-b982-185a5017a4ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_integrable_past_weighted_count
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_weighted_count_real_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Signed predictable-simple original marked jump weights built as the
difference of two finite-mean nonnegative parts have genuine real L¹ and rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (Wpos Wneg : Ω → ℝ≥0∞)
    (hWpos : Measurable[𝓕 s] Wpos)
    (hWneg : Measurable[𝓕 s] Wneg)
    (hPosFinite : (∫⁻ ω, Wpos ω ∂P) < ⊤)
    (hNegFinite : (∫⁻ ω, Wneg ω ∂P) < ⊤)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)) :
    Integrable (fun ω =>
      (Wpos ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
      (Wneg ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal) P ∧
    (∫ ω,
      (Wpos ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
      (Wneg ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal ∂P) =
      ((∫⁻ ω, Wpos ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal -
      ((∫⁻ ω, Wneg ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal := by
  have hIp :=
    avram_p2_e_compensator_integrable_past_weighted_count
      X s t hst B hB Wpos hWpos hPosFinite hν hRate
  have hIn :=
    avram_p2_e_compensator_integrable_past_weighted_count
      X s t hst B hB Wneg hWneg hNegFinite hν hRate
  have hMp :=
    avram_p2_e_compensator_finite_weighted_count_real_mean
      X s t hst B hB Wpos hWpos hPosFinite hν hRate
  have hMn :=
    avram_p2_e_compensator_finite_weighted_count_real_mean
      X s t hst B hB Wneg hWneg hNegFinite hν hRate
  constructor
  · exact hIp.sub hIn
  · rw [integral_sub hIp hIn, hMp, hMn]
