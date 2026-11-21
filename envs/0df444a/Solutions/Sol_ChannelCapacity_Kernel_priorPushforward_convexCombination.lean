-- Prove2me | solution 1 for ChannelCapacity.Kernel.priorPushforward_convexCombination
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:46.502909+00:00
-- url     : https://prove2.me/submissions/dbeab68a-c2d4-46fb-8c34-9de8ee942f30

module
public import Definitions.Def_LeanPool_ChannelCapacity_Basic
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
attribute [local simp] ProbabilityMeasure.convexCombination_toMeasure



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
theorem _root_.solution (k : Kernel α β) [IsMarkovKernel k]
    (p q : ProbabilityMeasure α) (t : NNReal) (ht : t ≤ 1) :
    Kernel.priorPushforward k (ProbabilityMeasure.convexCombination p q t ht) =
      ProbabilityMeasure.convexCombination
        (Kernel.priorPushforward k p)
        (Kernel.priorPushforward k q)
        t ht := by
  apply ProbabilityMeasure.toMeasure_injective
  change k ∘ₘ (ProbabilityMeasure.convexCombination p q t ht).toMeasure =
    (ProbabilityMeasure.convexCombination (Kernel.priorPushforward k p)
      (Kernel.priorPushforward k q) t ht).toMeasure
  rw [ProbabilityMeasure.convexCombination_toMeasure, Measure.comp_add]
  change k ∘ₘ ((t : ENNReal) • p.toMeasure) +
      k ∘ₘ ((((1 : NNReal) - t : NNReal) : ENNReal) • q.toMeasure) =
    (ProbabilityMeasure.convexCombination (Kernel.priorPushforward k p)
      (Kernel.priorPushforward k q) t ht).toMeasure
  rw [Measure.comp_smul, Measure.comp_smul, ProbabilityMeasure.convexCombination_toMeasure]
  change t • (k ∘ₘ p.toMeasure) + (1 - (t : ENNReal)) • (k ∘ₘ q.toMeasure) =
    t • (k ∘ₘ p.toMeasure) + (1 - (t : ENNReal)) • (k ∘ₘ q.toMeasure)
  rfl
end ChannelCapacity.Kernel
