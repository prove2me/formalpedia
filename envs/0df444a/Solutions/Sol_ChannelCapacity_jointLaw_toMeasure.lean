-- Prove2me | solution 1 for ChannelCapacity.jointLaw_toMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:52.729828+00:00
-- url     : https://prove2.me/submissions/44002447-4db2-4478-86ed-6aaf61d02bb8

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
theorem _root_.solution (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) :
    (jointLaw k p).toMeasure = p.toMeasure ⊗ₘ k :=
  rfl
end ChannelCapacity
