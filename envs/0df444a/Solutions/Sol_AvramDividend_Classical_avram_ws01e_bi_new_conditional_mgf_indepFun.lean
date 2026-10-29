-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_conditional_mgf_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:44:25.546695+00:00
-- url     : https://prove2.me/submissions/1a3254df-752f-49b7-8a5d-e0a070a5a402

import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.ComplexMGF
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_upper_ray_cylinders_indepFun

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- Conditional exponential moments identify each upper-ray conditional law,
and upper-ray cylinders generate independence. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R Y : Ω → ℝ) (hR : Measurable R) (hY : Measurable Y)
    (hMoment : ∀ a : ℝ, P (R ⁻¹' Set.Ioi a) ≠ 0 →
      ∀ s : ℝ, 0 < s →
        Integrable (fun y : ℝ => Real.exp (s * y))
          ((P[|R ⁻¹' Set.Ioi a]).map Y) ∧
        Integrable (fun y : ℝ => Real.exp (s * y)) (P.map Y))
    (hLap : ∀ a : ℝ, P (R ⁻¹' Set.Ioi a) ≠ 0 →
      ∀ s : ℝ, 0 < s →
        (∫ y : ℝ, Real.exp (s * y) ∂((P[|R ⁻¹' Set.Ioi a]).map Y)) =
          ∫ y : ℝ, Real.exp (s * y) ∂(P.map Y)) :
    IndepFun R Y P := by
  apply AvramDividend.Classical.avram_ws01e_b_upper_ray_cylinders_indepFun
    P R hR Y hY
  intro a B hB
  let A : Set Ω := R ⁻¹' Set.Ioi a
  have hA : MeasurableSet A := hR measurableSet_Ioi
  change P (A ∩ Y ⁻¹' B) = P A * P (Y ⁻¹' B)
  by_cases hz : P A = 0
  · have hzero : P (A ∩ Y ⁻¹' B) = 0 := by
      have hmono : P (A ∩ Y ⁻¹' B) ≤ P A :=
        measure_mono Set.inter_subset_left
      have hle : P (A ∩ Y ⁻¹' B) ≤ 0 := by simpa [hz] using hmono
      exact le_antisymm hle zero_le
    simp [hz, hzero]
  · haveI : IsProbabilityMeasure (P[|A]) :=
      ProbabilityTheory.cond_isProbabilityMeasure hz
    haveI : IsProbabilityMeasure ((P[|A]).map Y) :=
      Measure.isProbabilityMeasure_map hY.aemeasurable
    haveI : IsProbabilityMeasure (P.map Y) :=
      Measure.isProbabilityMeasure_map hY.aemeasurable
    have hlaw : (P[|A]).map Y = P.map Y :=
      AvramDividend.Classical.measure_eq_of_pos_mgf_on_ray
        (fun s hs => (hMoment a hz s hs).1)
        (fun s hs => (hMoment a hz s hs).2)
        (fun s hs => hLap a hz s hs)
    have hBmass : (P[|A]) (Y ⁻¹' B) = P (Y ⁻¹' B) := by
      have heval := congrArg (fun μ : Measure ℝ => μ B) hlaw
      simpa [Measure.map_apply hY hB] using heval
    calc
      P (A ∩ Y ⁻¹' B) = (P[|A]) (Y ⁻¹' B) * P A :=
        (ProbabilityTheory.cond_mul_eq_inter hA (Y ⁻¹' B) P).symm
      _ = P A * P (Y ⁻¹' B) := by rw [hBmass, mul_comm]
