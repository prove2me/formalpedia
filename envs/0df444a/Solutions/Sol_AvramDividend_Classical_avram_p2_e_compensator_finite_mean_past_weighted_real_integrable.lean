-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_finite_mean_past_weighted_real_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:46:10.392664+00:00
-- url     : https://prove2.me/submissions/ef4738c5-ff61-487b-8950-0cc3eda79a54

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_intrinsic_rectangle_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A past-weighted original intrinsic marked count is real L¹ whenever its
unweighted mean and the past weight mean are both finite, independent of ν. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W)
    (hWfinite : (∫⁻ ω, W ω ∂P) < ⊤)
    (hNfinite : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) < ⊤) :
    Integrable (fun ω => (W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal) P := by
  have hMeasW : Measurable W :=
    hW.mono (𝓕.le s) le_rfl
  have hMeasN :=
    avram_p2_e_compensator_intrinsic_rectangle_count_measurable
      X s t hst B hB
  apply integrable_toReal_of_lintegral_ne_top
    (hMeasW.mul hMeasN).aemeasurable
  simp only [Pi.mul_apply]
  rw [avram_p2_e_compensator_weighted_intrinsic_rectangle_factor
    X s t hst B hB W hW]
  exact ne_of_lt
    (ENNReal.mul_lt_top hWfinite hNfinite)