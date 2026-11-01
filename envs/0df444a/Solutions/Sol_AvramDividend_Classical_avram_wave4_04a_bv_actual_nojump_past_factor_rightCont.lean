-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_nojump_past_factor_rightCont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:23:29.913435+00:00
-- url     : https://prove2.me/submissions/5ef45828-aebb-4095-a873-6b4499e646c5

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_nojump_event_ae_eq_drift_increment
import Theorems.Thm_AvramDividend_Classical_levy_indepIncrements_rightCont

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Actual future no-jump events factor from the original right-continuous past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕.rightCont s) A) :
    P (A ∩ {ω : Ω |
      ∀ u : ℝ≥0, u ∈ Ioc s t →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0}) =
      P A * P {ω : Ω |
        ∀ u : ℝ≥0, u ∈ Ioc s t →
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0} := by
  classical
  let N : Set Ω := {ω : Ω | ∀ u : ℝ≥0, u ∈ Ioc s t →
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0}
  let B : Set Ω := {ω : Ω | X.X t ω - X.X s ω =
    ((t : ℝ) - (s : ℝ)) * X.drift}
  have hAE : N =ᵐ[P] B :=
    avram_wave4_04a_bv_actual_nojump_event_ae_eq_drift_increment
      X hBV hFinite s t hst
  have hBMeas :
      @MeasurableSet Ω
        (MeasurableSpace.comap (fun ω => X.X t ω - X.X s ω) inferInstance)
        B := by
    exact ⟨{((t : ℝ) - (s : ℝ)) * X.drift}, measurableSet_singleton _, rfl⟩
  have hFactor : P (B ∩ A) = P B * P A :=
    ((Indep_iff
        (MeasurableSpace.comap (fun ω => X.X t ω - X.X s ω) inferInstance)
        (𝓕.rightCont s) P).mp
      (levy_indepIncrements_rightCont X s t hst))
      B A hBMeas hA
  have hAEInter :
      (fun ω : Ω => ω ∈ A ∧ ω ∈ N) =ᵐ[P]
      (fun ω : Ω => ω ∈ A ∧ ω ∈ B) := by
    filter_upwards [hAE] with ω hω
    exact congrArg (fun p : Prop => ω ∈ A ∧ p) hω
  change P (A ∩ N) = P A * P N
  calc
    P (A ∩ N) = P (A ∩ B) := measure_congr hAEInter
    _ = P B * P A := by
      rw [Set.inter_comm A B]
      exact hFactor
    _ = P A * P N := by
      rw [mul_comm (P B) (P A), measure_congr hAE]
