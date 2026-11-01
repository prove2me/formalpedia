-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_marked_future_cross_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:47:53.510904+00:00
-- url     : https://prove2.me/submissions/90dbf70a-e18a-422e-8869-50b71f7e0bad

import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_product_integrable_ws01b
import Theorems.Thm_AvramDividend_Classical_poisson_predictable_marked_compensation_closed_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

/-- Any two jointly past-measurable L² weights are orthogonal to the centred
future marked-Poisson cell. No independence between the two weights is needed. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E)
    (H J : Ω → ℝ) (hHm : Measurable H) (hJm : Measurable J)
    (hH2 : MemLp H 2 μ) (hJ2 : MemLp J 2 μ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n)) (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hPast : IndepFun (fun ω => (H ω, J ω))
      (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (f : E → ℝ) (hf : Measurable f) (hfI : Integrable f ν) :
    Integrable (fun ω => (H ω * J ω) *
      ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
        (r : ℝ) * ∫ z, f z ∂ν)) μ ∧
      (∫ ω, (H ω * J ω) *
        ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
          (r : ℝ) * ∫ z, f z ∂ν) ∂μ) = 0 := by
  let W : Ω → ℝ := fun ω => H ω * J ω
  let S : Ω → ℝ := fun ω => ∑ n ∈ Finset.range (K ω), f (Y n ω)
  let c : ℝ := (r : ℝ) * ∫ z, f z ∂ν
  have hW : Integrable W μ := by
    have h := hH2.integrable_mul hJ2
    have hEq : (fun ω => H ω * J ω) = H * J := by
      funext ω
      rfl
    change Integrable (fun ω => H ω * J ω) μ
    rw [hEq]
    exact h
  have hWm : Measurable W := hHm.mul hJm
  have hIndep : IndepFun W
      (fun ω => (K ω, fun n : ℕ => Y n ω)) μ := by
    simpa [Function.comp_def, W] using
      hPast.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => p.1 * p.2)) measurable_id
  have hWS : Integrable (fun ω => W ω * S ω) μ :=
    poisson_predictable_marked_product_integrable_ws01b
      μ ν W hWm hW K Y hKm r hKlaw hYm hYL hCountMarks hIndep f hf hfI
  have hWc : Integrable (fun ω => W ω * c) μ := by
    have h := hW.const_mul c
    simpa only [mul_comm] using h
  have hEq : (fun ω => W ω * (S ω - c)) =
      (fun ω => W ω * S ω) - (fun ω => W ω * c) := by
    funext ω
    dsimp
    ring
  have hMean : (∫ ω, W ω * S ω ∂μ) =
      (∫ ω, W ω ∂μ) * c :=
    poisson_predictable_marked_compensation_closed_ws01b
      μ ν W hWm hW K Y hKm r hKlaw hYm hYL hCountMarks hIndep f hf hfI
  constructor
  · rw [hEq]
    exact hWS.sub hWc
  · change (∫ ω, W ω * (S ω - c) ∂μ) = 0
    calc
      _ = (∫ ω, W ω * S ω ∂μ) -
          (∫ ω, W ω * c ∂μ) := by
        rw [hEq]
        change (∫ ω, W ω * S ω - W ω * c ∂μ) =
          (∫ ω, W ω * S ω ∂μ) - (∫ ω, W ω * c ∂μ)
        exact integral_sub hWS hWc
      _ = 0 := by
        rw [hMean, integral_mul_const]
        ring