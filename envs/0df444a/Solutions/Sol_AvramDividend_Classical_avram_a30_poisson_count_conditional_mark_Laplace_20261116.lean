-- Prove2me | solution 1 for AvramDividend.Classical.avram_a30_poisson_count_conditional_mark_Laplace_20261116
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:18:57.015464+00:00
-- url     : https://prove2.me/submissions/87699fcc-1d58-4d76-a15d-764b3092efc3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section
theorem AvramDividend.Classical.avram_a30_poisson_count_conditional_mark_Laplace_20261116
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (m : ℝ)
    (f : Ω → ℝ) (hf : Integrable f P)
    (hm : Integrable (fun k : ℕ => m ^ k) (poissonMeasure r))
    (hCell : ∀ k : ℕ,
      (∫ ω in {ω : Ω | K ω = k}, f ω ∂P) =
        (poissonMeasure r).real {k} * m ^ k) :
    (∫ ω, f ω ∂P) = Real.exp ((r : ℝ) * (m - 1)) := by
  have hU : (⋃ k : ℕ, {ω : Ω | K ω = k}) = univ := by
    ext ω; simp
  have hmeas : ∀ k : ℕ, MeasurableSet {ω : Ω | K ω = k} :=
    fun k => hK (measurableSet_singleton k)
  have hdisj : Pairwise (Function.onFun Disjoint fun k : ℕ => {ω : Ω | K ω = k}) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω ha hb
    exact hab (ha.symm.trans hb)
  have h1 := integral_iUnion hmeas hdisj (by rw [hU]; exact hf.integrableOn)
  rw [hU, Measure.restrict_univ] at h1
  rw [h1]
  simp_rw [hCell]
  rw [← AvramDividend.Classical.chat06_poisson_count_pgf_general r m,
    integral_countable' hm]
  simp [smul_eq_mul]

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (m : ℝ)
    (f : Ω → ℝ) (hf : Integrable f P)
    (hm : Integrable (fun k : ℕ => m ^ k) (poissonMeasure r))
    (hCell : ∀ k : ℕ,
      (∫ ω in {ω : Ω | K ω = k}, f ω ∂P) =
        (poissonMeasure r).real {k} * m ^ k) :
    (∫ ω, f ω ∂P) = Real.exp ((r : ℝ) * (m - 1)) :=
  AvramDividend.Classical.avram_a30_poisson_count_conditional_mark_Laplace_20261116 P K hK r m f hf hm hCell
