-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:06:36.420925+00:00
-- url     : https://prove2.me/submissions/941de1ef-d408-40c3-9db9-1c4b039bd243

import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_compound_poisson_centered_l2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_poisson_random_mark_sum_square_integrable
import Theorems.Thm_AvramDividend_Classical_poisson_random_mark_sum_integrable_ws01b
import Theorems.Thm_AvramDividend_Classical_variable_finite_marks_sum_measurable_ws01b
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat
/-- Predictable past-weighted quadratic energy of a full independent marked Poisson cell. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (H : Ω → ℝ) (hHm : Measurable H)
    (hH2 : Integrable (fun ω => H ω ^ 2) μ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n)) (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hYi : iIndepFun Y μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hPast : IndepFun H (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) (hf2 : MemLp f 2 ν) :
    Integrable (fun ω =>
      (H ω * ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
        (r : ℝ) * ∫ z, f z ∂ν)) ^ 2) μ ∧
      (∫ ω, (H ω * ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
        (r : ℝ) * ∫ z, f z ∂ν)) ^ 2 ∂μ) =
        (∫ ω, H ω ^ 2 ∂μ) * ((r : ℝ) * ∫ z, f z ^ 2 ∂ν) := by
  let S : Ω → ℝ := fun ω => ∑ n ∈ Finset.range (K ω), f (Y n ω)
  let c : ℝ := (r : ℝ) * ∫ z, f z ∂ν
  have hS : Integrable S μ :=
    poisson_random_mark_sum_integrable_ws01b
      μ ν K Y hKm r hKlaw hYm hYL hCountMarks f hf hfI
  have hS2 : Integrable (fun ω => S ω ^ 2) μ :=
    avram_wave4_p1_poisson_random_mark_sum_square_integrable
      μ ν K Y hKm r hKlaw hYm hYL hCountMarks f hf hf2
  have hC2 : Integrable (fun ω => (S ω - c) ^ 2) μ := by
    have hPoly := (hS2.sub (hS.const_mul (2 * c))).add (integrable_const (c ^ 2))
    have hEq : (fun ω => (S ω - c) ^ 2) =
        (fun ω => S ω ^ 2 - (2 * c) * S ω + c ^ 2) := by
      funext ω
      ring
    rw [hEq]
    exact hPoly
  have hg := variable_finite_marks_sum_measurable_ws01b f hf
  have hFutureMeas : Measurable (fun x : ℕ × (ℕ → E) =>
      ((∑ n ∈ Finset.range x.1, f (x.2 n)) - c) ^ 2) := by
    exact (hg.sub measurable_const).pow_const 2
  have hIndep : IndepFun (fun ω => H ω ^ 2)
      (fun ω => (S ω - c) ^ 2) μ := by
    simpa only [S, Function.comp_def] using hPast.comp
      (by fun_prop : Measurable (fun x : ℝ => x ^ 2)) hFutureMeas
  have hProdFun : (fun ω => H ω ^ 2 * (S ω - c) ^ 2) =
      (fun ω => H ω ^ 2) * (fun ω => (S ω - c) ^ 2) := by
    funext ω
    rfl
  have hProdInt : Integrable
      (fun ω => H ω ^ 2 * (S ω - c) ^ 2) μ := by
    have h := hIndep.integrable_mul hH2 hC2
    rw [hProdFun]
    exact h
  have hProdMean :
      (∫ ω, H ω ^ 2 * (S ω - c) ^ 2 ∂μ) =
      (∫ ω, H ω ^ 2 ∂μ) * (∫ ω, (S ω - c) ^ 2 ∂μ) := by
    rw [hProdFun]
    exact hIndep.integral_fun_mul_eq_mul_integral
        hH2.aestronglyMeasurable hC2.aestronglyMeasurable
  have hEnergy : (∫ ω, (S ω - c) ^ 2 ∂μ) =
      (r : ℝ) * ∫ z, f z ^ 2 ∂ν :=
    avram_wave4_p1_compound_poisson_centered_l2_isometry
      μ ν K Y hKm r hKlaw hYm hYL hYi hCountMarks f hf hfI hf2
  have hEq : (fun ω => (H ω * (S ω - c)) ^ 2) =
      (fun ω => H ω ^ 2 * (S ω - c) ^ 2) := by
    funext ω
    ring
  constructor
  · rw [hEq]
    exact hProdInt
  · rw [hEq, hProdMean, hEnergy]