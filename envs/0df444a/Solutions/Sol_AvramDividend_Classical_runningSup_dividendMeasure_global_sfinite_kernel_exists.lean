-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_global_sfinite_kernel_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:57:59.047036+00:00
-- url     : https://prove2.me/submissions/cc903304-987a-477f-9e5e-e94d3f395dd5

import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_kernel_isSFinite_of_pointwise_finite
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_lt_top
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_restrict_Ioc_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ κ : ProbabilityTheory.Kernel Ω ℝ,
      ProbabilityTheory.IsSFiniteKernel κ ∧
      ∀ ω : Ω, κ ω = dividendMeasure (runningSup X) ω := by
  let S : ℤ → Set ℝ := fun n => Set.Ioc (n : ℝ) ((n : ℝ) + 1)
  let κs : ℤ → ProbabilityTheory.Kernel Ω ℝ := fun n =>
    ProbabilityTheory.Kernel.mk
      (fun ω : Ω => (dividendMeasure (runningSup X) ω).restrict (S n))
      (runningSup_dividendMeasure_restrict_Ioc_measurable
        X (n : ℝ) ((n : ℝ) + 1))
  have hlocal (n : ℤ) :
      ProbabilityTheory.IsSFiniteKernel (κs n) := by
    apply kernel_isSFinite_of_pointwise_finite (κs n)
    intro ω
    change ((dividendMeasure (runningSup X) ω).restrict (S n)) Set.univ < ⊤
    simpa [S] using
      (runningSup_dividendMeasure_Ioc_lt_top X ω (n : ℝ) ((n : ℝ) + 1))
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
    (μ := dividendMeasure (runningSup X) ω) hd hm
  have hsum :
      dividendMeasure (runningSup X) ω =
        Measure.sum (fun n : ℤ =>
          (dividendMeasure (runningSup X) ω).restrict (S n)) := by
    simpa only [hu, Measure.restrict_univ] using hr
  change (ProbabilityTheory.Kernel.sum κs) ω =
    dividendMeasure (runningSup X) ω
  rw [ProbabilityTheory.Kernel.sum_apply κs ω]
  change Measure.sum (fun n : ℤ =>
    (dividendMeasure (runningSup X) ω).restrict (S n)) =
      dividendMeasure (runningSup X) ω
  exact hsum.symm
