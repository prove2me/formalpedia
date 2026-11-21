-- Prove2me | solution 1 for ChannelCapacity.Kernel.outputMarginalReference_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:16.09383+00:00
-- url     : https://prove2.me/submissions/c02d6f77-b50a-42e4-b8e3-21424b243822

module
public import Definitions.Def_LeanPool_ChannelCapacity_Basic
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
open ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
open ChannelCapacity.Kernel
namespace ChannelCapacity.Kernel
theorem _root_.solution
    (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    Kernel.OutputMarginalReference k p (outputPrior k p).toMeasure := by
  exact ⟨p, Measure.AbsolutelyContinuous.rfl, rfl⟩
end ChannelCapacity.Kernel
