-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_finite_weighted_centered_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:40:38.403449+00:00
-- url     : https://prove2.me/submissions/47473abf-55ec-42a5-8238-fd867e6d5ee9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_integrable_past_weighted_count
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_weighted_count_real_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine original marked jump count, centred by its predictable
finite-mean intensity, is L¹ with zero mean on each past-weighted rectangle. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W)
    (hWfinite : (∫⁻ ω, W ω ∂P) < ⊤)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)) :
    Integrable (fun ω => (W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
      ((∫⁻ ω, W ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal) P ∧
    (∫ ω, (W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
      ((∫⁻ ω, W ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal ∂P) = 0 := by
  haveI : IsProbabilityMeasure P := X.isProbability
  let c : ℝ := ((∫⁻ ω, W ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal
  have hInt :=
    avram_p2_e_compensator_integrable_past_weighted_count
      X s t hst B hB W hW hWfinite hν hRate
  have hMean :=
    avram_p2_e_compensator_finite_weighted_count_real_mean
      X s t hst B hB W hW hWfinite hν hRate
  constructor
  · exact hInt.sub (integrable_const c)
  · calc
      (∫ ω, (W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal - c ∂P) =
        (∫ ω, (W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal ∂P) - (∫ _ : Ω, c ∂P) :=
          integral_sub hInt (integrable_const c)
      _ = c - c := by rw [hMean]; simp [c]
      _ = 0 := sub_self c
