-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_two_cell_marked_l2_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:15:20.411124+00:00
-- url     : https://prove2.me/submissions/105716fd-a0fd-4899-9696-56fc8e633bcc

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_marked_future_cross_orthogonality

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

/-- An independent future marked-Poisson cell adds exactly its predictable
quadratic energy to a square-integrable past payoff. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (H J : Ω → ℝ) (hHm : Measurable H) (hJm : Measurable J)
    (hH2 : MemLp H 2 μ) (hHSq : Integrable (fun ω => H ω ^ 2) μ)
    (hJ2 : MemLp J 2 μ) (hJSq : Integrable (fun ω => J ω ^ 2) μ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n)) (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hYi : iIndepFun Y μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hPast : IndepFun (fun ω => (H ω, J ω))
      (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) (hf2 : MemLp f 2 ν) :
    Integrable (fun ω => (H ω + J ω *
        ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
          (r : ℝ) * ∫ z, f z ∂ν)) ^ 2) μ ∧
      (∫ ω, (H ω + J ω *
        ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
          (r : ℝ) * ∫ z, f z ∂ν)) ^ 2 ∂μ) =
        (∫ ω, H ω ^ 2 ∂μ) +
          (∫ ω, J ω ^ 2 ∂μ) * ((r : ℝ) * ∫ z, f z ^ 2 ∂ν) := by
  let S : Ω → ℝ := fun ω => ∑ n ∈ Finset.range (K ω), f (Y n ω)
  let c : ℝ := (r : ℝ) * ∫ z, f z ∂ν
  have hIndepJ : IndepFun J (fun ω => (K ω, fun n : ℕ => Y n ω)) μ := by
    simpa [Function.comp_def] using
      hPast.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => p.2)) measurable_id
  have hNext := avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry
    μ ν J hJm hJSq K Y hKm r hKlaw hYm hYL hYi hCountMarks hIndepJ f hf hfI hf2
  have hCross := avram_wave4_p1_marked_future_cross_orthogonality
    μ ν H J hHm hJm hH2 hJ2 K Y hKm r hKlaw hYm hYL hCountMarks hPast f hf hfI
  have hDouble : Integrable (fun ω =>
      (2 : ℝ) * ((H ω * J ω) * (S ω - c))) μ :=
    hCross.1.const_mul 2
  have hEq : (fun ω => (H ω + J ω * (S ω - c)) ^ 2) =
      ((fun ω => H ω ^ 2) + (fun ω => (J ω * (S ω - c)) ^ 2)) +
        (fun ω => (2 : ℝ) * ((H ω * J ω) * (S ω - c))) := by
    funext ω
    dsimp
    ring
  constructor
  · rw [hEq]
    exact (hHSq.add hNext.1).add hDouble
  · have hOuter :
        (∫ ω, (H ω ^ 2 + (J ω * (S ω - c)) ^ 2) +
          (2 : ℝ) * ((H ω * J ω) * (S ω - c)) ∂μ) =
        (∫ ω, H ω ^ 2 + (J ω * (S ω - c)) ^ 2 ∂μ) +
        (∫ ω, (2 : ℝ) * ((H ω * J ω) * (S ω - c)) ∂μ) := by
      simpa only [Pi.add_apply] using integral_add (hHSq.add hNext.1) hDouble
    have hInner :
        (∫ ω, H ω ^ 2 + (J ω * (S ω - c)) ^ 2 ∂μ) =
        (∫ ω, H ω ^ 2 ∂μ) + (∫ ω, (J ω * (S ω - c)) ^ 2 ∂μ) := by
      simpa only [Pi.add_apply] using integral_add hHSq hNext.1
    rw [hEq]
    change (∫ ω, (H ω ^ 2 + (J ω * (S ω - c)) ^ 2) +
      (2 : ℝ) * ((H ω * J ω) * (S ω - c)) ∂μ) = _
    rw [hOuter, hInner, integral_const_mul, hNext.2, hCross.2]
    ring
