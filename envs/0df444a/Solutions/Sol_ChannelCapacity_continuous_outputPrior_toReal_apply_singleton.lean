-- Prove2me | solution 1 for ChannelCapacity.continuous_outputPrior_toReal_apply_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:38.011776+00:00
-- url     : https://prove2.me/submissions/c3fd988b-e075-4bcd-9b05-b49c4338823b

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_toReal_outputPrior_apply_singleton
public import Theorems.Thm_ChannelCapacity_continuous_toReal_apply_singleton

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
variable [TopologicalSpace α] [TopologicalSpace β]
  [DiscreteTopology α] [DiscreteTopology β]
  [BorelSpace α] [BorelSpace β]
  [CompactSpace α] [CompactSpace β]
omit [Fintype α] [Fintype β] [TopologicalSpace β] [DiscreteTopology β] [BorelSpace β]
  [CompactSpace β]
namespace ChannelCapacity
theorem _root_.solution [Finite α]
    (k : Kernel α β) [IsMarkovKernel k] (b : β) :
    Continuous fun p : ProbabilityMeasure α => ((outputPrior k p).toMeasure {b}).toReal := by
  let _instFintypeα : Fintype α := Fintype.ofFinite α
  have hsum :
      Continuous fun p : ProbabilityMeasure α =>
        ∑ a, (p.toMeasure {a}).toReal * (k a {b}).toReal :=
    continuous_finsetSum (s := (Finset.univ : Finset α)) fun a _ha =>
      (continuous_toReal_apply_singleton a).mul continuous_const
  convert hsum using 1
  ext p
  exact toReal_outputPrior_apply_singleton k p b
end ChannelCapacity
