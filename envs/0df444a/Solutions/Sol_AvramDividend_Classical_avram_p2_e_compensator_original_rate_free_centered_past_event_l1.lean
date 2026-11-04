-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_rate_free_centered_past_event_l1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:06:18.956973+00:00
-- url     : https://prove2.me/submissions/74aff091-3bad-4852-9fff-11ae67a62dcb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The finite-mean original intrinsic marked count centred by its true mean
is integrable and has zero signed integral on all true past-filtration events. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hMeanFinite :  (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) < ⊤) :
    Integrable (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
        ((∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P)).toReal) P ∧
    ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫ ω in A, (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
        ((∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P)).toReal ∂P) = 0 := by
  haveI : IsProbabilityMeasure P := X.isProbability
  let r : ℝ≥0∞ :=  (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P)
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
  have hNmeas : Measurable N :=
    avram_p2_e_compensator_intrinsic_rectangle_count_measurable
      X s t hst B hB
  have hNint : Integrable (fun ω => (N ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hNmeas.aemeasurable
      (ne_of_lt hMeanFinite)
  constructor
  · exact hNint.sub (integrable_const r.toReal)
  · intro A hA
    have hRect : (∫⁻ ω in A, N ω ∂P) = P A * r := by
      obtain ⟨F, hF, hExtract⟩ :=
        avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
          X s t hst B hB
      exact avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
        X s t hst A hA B hB F hF hExtract
    have hNfinite : (∫⁻ ω in A, N ω ∂P) ≠ ⊤ := by
      rw [hRect]
      exact ne_of_lt (ENNReal.mul_lt_top (measure_lt_top P A) hMeanFinite)
    have hRealA : (∫ ω in A, (N ω).toReal ∂P) = (P A * r).toReal := by
      calc
        (∫ ω in A, (N ω).toReal ∂P) =
            (∫⁻ ω in A, N ω ∂P).toReal :=
          integral_toReal hNmeas.aemeasurable (ae_lt_top hNmeas hNfinite)
        _ = (P A * r).toReal := congrArg ENNReal.toReal hRect
    calc
      (∫ ω in A, (N ω).toReal - r.toReal ∂P) =
          (∫ ω in A, (N ω).toReal ∂P) -
            (∫ ω in A, r.toReal ∂P) :=
        integral_sub hNint.integrableOn (integrable_const r.toReal).integrableOn
      _ = 0 := by
        rw [hRealA]
        simp [setIntegral_const, Measure.real, ENNReal.toReal_mul,
          mul_comm, mul_left_comm, mul_assoc]
