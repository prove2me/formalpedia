-- Prove2me | solution 1 for AvramDividend.Classical.kernel_sum_restrict_of_measurable_time_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:55:43.659987+00:00
-- url     : https://prove2.me/submissions/0717b1f9-ea38-4ca0-a2ce-b58c1c8af3d8

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.Restrict

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    (S : ℤ → Set ℝ)
    (hd : Pairwise (Function.onFun Disjoint S))
    (hm : ∀ n : ℤ, MeasurableSet (S n))
    (hu : (⋃ n : ℤ, S n) = Set.univ)
    (κs : ℤ → ProbabilityTheory.Kernel Ω ℝ)
    (heq : ∀ (n : ℤ) (ω : Ω),
      κs n ω = (κ ω).restrict (S n)) :
    κ = ProbabilityTheory.Kernel.sum κs := by
  apply ProbabilityTheory.Kernel.ext
  intro ω
  have hr :
      κ ω = Measure.sum (fun n : ℤ => (κ ω).restrict (S n)) := by
    have h := Measure.restrict_iUnion (μ := κ ω) hd hm
    simpa only [hu, Measure.restrict_univ] using h
  have hf :
      (fun n : ℤ => (κ ω).restrict (S n)) =
        (fun n : ℤ => κs n ω) := by
    funext n
    exact (heq n ω).symm
  rw [ProbabilityTheory.Kernel.sum_apply κs ω]
  simpa only [hf] using hr
