-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_centered_count_past_event_l1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:04:38.980989+00:00
-- url     : https://prove2.me/submissions/b1197b0e-78b5-4643-839d-c9348014f2b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_finite_nu_past_real_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every finite-rate compensated original intrinsic marked count increment
is real L1 and has zero real integral over all original past-filtration
events, the exact signed-event martingale-difference test. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    Integrable (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) P ∧
    ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫ ω in A, (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal ∂P) = 0 := by
  haveI : IsProbabilityMeasure P := X.isProbability
  let c : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
  have hInt : Integrable (fun ω => (N ω).toReal) P :=
    avram_p2_e_compensator_finite_nu_count_real_integrable
      X s t hst B hB hν hRate
  constructor
  · exact hInt.sub (integrable_const c)
  · intro A hA
    have hMeanA : (∫ ω in A, (N ω).toReal ∂P) =
        (P A * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal :=
      avram_p2_e_compensator_original_finite_nu_past_real_mean
        X s t hst A hA B hB hν hRate
    calc
      (∫ ω in A, (N ω).toReal - c ∂P) =
          (∫ ω in A, (N ω).toReal ∂P) - (∫ ω in A, c ∂P) :=
        integral_sub hInt.integrableOn (integrable_const c).integrableOn
      _ = 0 := by
        rw [hMeanA]
        simp [c, setIntegral_const, Measure.real, ENNReal.toReal_mul,
          mul_comm, mul_left_comm, mul_assoc]
