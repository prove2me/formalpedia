-- Prove2me | solution 1 for ChannelCapacity.independentJointLaw_toMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:43.678175+00:00
-- url     : https://prove2.me/submissions/34b94893-c39e-4246-a3b8-891ce3c2869c

module
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Basic

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
open ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
namespace ChannelCapacity
theorem _root_.solution (k : Kernel α β) [IsMarkovKernel k]
    (p : ProbabilityMeasure α) :
    (independentJointLaw k p).toMeasure =
      p.toMeasure ⊗ₘ Kernel.const α (outputPrior k p).toMeasure :=
  rfl
end ChannelCapacity
