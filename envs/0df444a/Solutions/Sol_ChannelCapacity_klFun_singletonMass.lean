-- Prove2me | solution 1 for ChannelCapacity.klFun_singletonMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:23.527368+00:00
-- url     : https://prove2.me/submissions/6e1d0f3f-0277-4d6e-80c0-d2a14c9b84c2

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
omit [Fintype α] [MeasurableSingletonClass α]
namespace ChannelCapacity
theorem _root_.solution (μ : ProbabilityMeasure α) (a : α) :
    InformationTheory.klFun ((μ.toMeasure {a}).toReal) =
      1 - (μ.toMeasure {a}).toReal - Real.negMulLog ((μ.toMeasure {a}).toReal) := by
  rw [InformationTheory.klFun, Real.negMulLog]
  ring
end ChannelCapacity
