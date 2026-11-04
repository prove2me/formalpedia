-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_integrable_past_weighted_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:31:33.457193+00:00
-- url     : https://prove2.me/submissions/05f5890a-f98e-46a7-8259-dcf6b2f83aab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_rate_from_unconditional

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every integrable nonnegative past weight times the genuine original marked
count on a finite-rate band has a real L¹ representative. -/
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
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
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
  rw [avram_p2_e_compensator_weighted_rate_from_unconditional
    X s t hst B hB W hW hRate]
  exact ne_of_lt
    (ENNReal.mul_lt_top hWfinite
      (ENNReal.mul_lt_top ENNReal.coe_lt_top hν))
