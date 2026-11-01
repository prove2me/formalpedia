-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_future_poisson_past_product_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:58:22.857049+00:00
-- url     : https://prove2.me/submissions/238ad0e3-1065-4b38-bd54-af6fe669a3ec

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

/-- A centred future Poisson count is orthogonal to products of any
two square-integrable past variables, even when those past variables
are mutually dependent. Independence is required of their joint past. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H J : Ω → ℝ) (hH2 : MemLp H 2 P) (hJ2 : MemLp J 2 P)
    (K : Ω → ℕ) (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) P)
    (hKInt : Integrable (fun ω => (K ω : ℝ) - (r : ℝ)) P)
    (hPast : IndepFun (fun ω => (H ω, J ω)) K P) :
    Integrable (fun ω => (H ω * J ω) * ((K ω : ℝ) - (r : ℝ))) P ∧
      (∫ ω, (H ω * J ω) * ((K ω : ℝ) - (r : ℝ)) ∂P) = 0 := by
  have hHJ : Integrable (fun ω => H ω * J ω) P := by
    have h := hH2.integrable_mul hJ2
    have heq : (fun ω => H ω * J ω) = H * J := by
      funext ω
      rfl
    rw [heq]
    exact h
  have hIndep : IndepFun (fun ω => H ω * J ω)
      (fun ω => (K ω : ℝ) - (r : ℝ)) P := by
    simpa [Function.comp_def] using
      hPast.comp
        (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1 * p.2))
        (by fun_prop : Measurable (fun n : ℕ => (n : ℝ) - (r : ℝ)))
  have hKRaw : Integrable (fun ω => (K ω : ℝ)) P := by
    have hh := hKInt.add (integrable_const (r : ℝ))
    have heq : (fun ω => (K ω : ℝ)) =
        (fun ω => (K ω : ℝ) - (r : ℝ)) + (fun _ : Ω => (r : ℝ)) := by
      funext ω
      dsimp
      ring
    rw [heq]
    exact hh
  have hKMean : (∫ ω, (K ω : ℝ) ∂P) = (r : ℝ) := by
    calc
      _ = ∫ n : ℕ, (n : ℝ) ∂poissonMeasure r := by
        simpa [Function.comp_def] using
          ((hKlaw.integral_comp
            (by fun_prop : AEStronglyMeasurable (fun n : ℕ => (n : ℝ))
              (poissonMeasure r))))
      _ = _ := AvramDividend.Classical.poisson_count_expected_rate_ws01b r
  have hKZero : (∫ ω, ((K ω : ℝ) - (r : ℝ)) ∂P) = 0 := by
    rw [integral_sub hKRaw (integrable_const _), hKMean, integral_const]
    simp
  have hCrossInt : Integrable
      (fun ω => (H ω * J ω) * ((K ω : ℝ) - (r : ℝ))) P := by
    have h := hIndep.integrable_mul hHJ hKInt
    have heq : (fun ω => (H ω * J ω) * ((K ω : ℝ) - (r : ℝ))) =
        (fun ω => H ω * J ω) *
          (fun ω => (K ω : ℝ) - (r : ℝ)) := by
      funext ω
      rfl
    rw [heq]
    exact h
  constructor
  · exact hCrossInt
  · have hFactor := hIndep.integral_fun_mul_eq_mul_integral
      hHJ.aestronglyMeasurable hKInt.aestronglyMeasurable
    simpa only [hKZero, mul_zero] using hFactor