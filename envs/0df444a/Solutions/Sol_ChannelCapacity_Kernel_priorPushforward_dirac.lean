-- Prove2me | solution 1 for ChannelCapacity.Kernel.priorPushforward_dirac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:50.304516+00:00
-- url     : https://prove2.me/submissions/3fe07ce9-13ea-4770-8ffc-b469043abadc

module
public import Definitions.Def_LeanPool_ChannelCapacity_Basic
public import Mathlib.MeasureTheory.Measure.DiracProba
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
public import Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
attribute [local simp] ChannelCapacity.independentJointLaw_toMeasure
attribute [local simp] ChannelCapacity.jointLaw_toMeasure
attribute [local simp] ChannelCapacity.outputPrior_toMeasure
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
theorem _root_.solution (k : Kernel α β) [IsMarkovKernel k] (a : α) :
    Kernel.priorPushforward k (MeasureTheory.diracProba a) =
      (⟨k a, ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure (κ := k) a⟩ :
        ProbabilityMeasure β) := by
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  have hd : (MeasureTheory.diracProba a).toMeasure = Measure.dirac a := rfl
  simpa [priorPushforward, outputPrior, hd] using
    congrArg (fun μ : Measure β => μ s) (Measure.dirac_bind k.measurable a)
end ChannelCapacity.Kernel
