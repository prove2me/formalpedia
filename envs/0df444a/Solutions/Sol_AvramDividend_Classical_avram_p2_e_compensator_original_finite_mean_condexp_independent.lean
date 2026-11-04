-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_finite_mean_condexp_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:47:40.528782+00:00
-- url     : https://prove2.me/submissions/e0d504c2-539b-4734-a981-5a32078e6f15

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

/-- The real original intrinsic marked future count has conditional expectation
its unconditional mean at the actual past filtration, without identifying ν. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hMeanFinite : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) < ⊤) :
    (condExp (𝓕 s) P (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)) =ᵐ[P]
      (fun _ : Ω => (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P).toReal) := by
  haveI : IsProbabilityMeasure P := X.isProbability
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
  let r : ℝ≥0∞ := ∫⁻ ω, N ω ∂P
  have hNmeas : Measurable N :=
    avram_p2_e_compensator_intrinsic_rectangle_count_measurable
      X s t hst B hB
  have hNint : Integrable (fun ω => (N ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hNmeas.aemeasurable
      (ne_of_lt hMeanFinite)
  letI : IsFiniteMeasure (P.trim (𝓕.le s)) :=
    MeasureTheory.isFiniteMeasure_trim (𝓕.le s)
  have hRect (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
      (∫⁻ ω in A, N ω ∂P) = P A * r := by
    obtain ⟨F, hF, hExtract⟩ :=
      avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
        X s t hst B hB
    exact avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
      X s t hst A hA B hB F hF hExtract
  have hEqA (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
      (_hPA : P A < ⊤) :
      (∫ ω in A, r.toReal ∂P) = (∫ ω in A, (N ω).toReal ∂P) := by
    have hNfinite : (∫⁻ ω in A, N ω ∂P) ≠ ⊤ := by
      rw [hRect A hA]
      exact ne_of_lt (ENNReal.mul_lt_top (measure_lt_top P A) hMeanFinite)
    have hToReal : (∫ ω in A, (N ω).toReal ∂P) =
        (P A * r).toReal := by
      calc
        (∫ ω in A, (N ω).toReal ∂P) =
            (∫⁻ ω in A, N ω ∂P).toReal :=
          integral_toReal hNmeas.aemeasurable (ae_lt_top hNmeas hNfinite)
        _ = (P A * r).toReal := congrArg ENNReal.toReal (hRect A hA)
    rw [hToReal]
    simp [MeasureTheory.setIntegral_const, Measure.real, ENNReal.toReal_mul,
      mul_comm, mul_left_comm, mul_assoc]
  have hConstant : AEStronglyMeasurable[𝓕 s]
      (fun _ : Ω => r.toReal) P :=
    stronglyMeasurable_const.aestronglyMeasurable
  have hCond := ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s)
    hNint
    (by
      intro A hA hPA
      exact (integrable_const r.toReal).integrableOn)
    (by
      intro A hA hPA
      exact hEqA A hA hPA)
    hConstant
  exact hCond.symm
