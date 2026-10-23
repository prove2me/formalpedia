-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_global_sfinite_kernel_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T23:35:08.95988+00:00
-- url     : https://prove2.me/submissions/510e1542-7a9c-4244-b75d-8b6a5bcc3176

import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.Restrict
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_kernel_isSFinite_of_pointwise_finite
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_lt_top
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_restrict_Ioc_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∃ κ : ProbabilityTheory.Kernel Ω ℝ,
      ProbabilityTheory.IsSFiniteKernel κ ∧
      ∀ ω : Ω, κ ω = dividendMeasure D ω := by
  let S : ℤ → Set ℝ := fun n => Set.Ioc (n : ℝ) ((n : ℝ) + 1)
  let κs : ℤ → ProbabilityTheory.Kernel Ω ℝ := fun n =>
    ProbabilityTheory.Kernel.mk
      (fun ω : Ω => (dividendMeasure D ω).restrict (S n))
      (dividendMeasure_restrict_Ioc_measurable
        D hD (n : ℝ) ((n : ℝ) + 1))
  have hlocal (n : ℤ) :
      ProbabilityTheory.IsSFiniteKernel (κs n) := by
    apply kernel_isSFinite_of_pointwise_finite (κs n)
    intro ω
    change ((dividendMeasure D ω).restrict (S n)) Set.univ < ⊤
    simpa [S] using
      (dividendMeasure_Ioc_lt_top D hD ω (n : ℝ) ((n : ℝ) + 1))
  letI : ∀ n : ℤ, ProbabilityTheory.IsSFiniteKernel (κs n) := hlocal
  let κ : ProbabilityTheory.Kernel Ω ℝ :=
    ProbabilityTheory.Kernel.sum κs
  have hκ : ProbabilityTheory.IsSFiniteKernel κ := by
    change ProbabilityTheory.IsSFiniteKernel
      (ProbabilityTheory.Kernel.sum κs)
    exact ProbabilityTheory.Kernel.isSFiniteKernel_sum
  refine ⟨κ, hκ, ?_⟩
  intro ω
  have hd : Pairwise (Function.onFun Disjoint S) := by
    exact Set.pairwise_disjoint_Ioc_intCast ℝ
  have hm : ∀ n : ℤ, MeasurableSet (S n) := by
    intro n
    exact measurableSet_Ioc
  have hu : (⋃ n : ℤ, S n) = Set.univ := by
    exact iUnion_Ioc_intCast ℝ
  have hr := Measure.restrict_iUnion
    (μ := dividendMeasure D ω) hd hm
  have hsum :
      dividendMeasure D ω =
        Measure.sum (fun n : ℤ =>
          (dividendMeasure D ω).restrict (S n)) := by
    simpa only [hu, Measure.restrict_univ] using hr
  change (ProbabilityTheory.Kernel.sum κs) ω =
    dividendMeasure D ω
  rw [ProbabilityTheory.Kernel.sum_apply κs ω]
  change Measure.sum (fun n : ℤ =>
    (dividendMeasure D ω).restrict (S n)) =
      dividendMeasure D ω
  exact hsum.symm

