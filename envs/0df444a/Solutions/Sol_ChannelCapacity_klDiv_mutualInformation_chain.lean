-- Prove2me | solution 1 for ChannelCapacity.klDiv_mutualInformation_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:00.495575+00:00
-- url     : https://prove2.me/submissions/fe4bc6af-eb57-4868-9f94-9120e5abcd35

module
public import Definitions.Def_LeanPool_ChannelCapacity_Basic
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.Probability.Kernel.Posterior
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
public import Theorems.Thm_InformationTheory_klDiv_map_measurableEquiv
public import Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
attribute [local simp] ChannelCapacity.independentJointLaw_toMeasure
attribute [local simp] ChannelCapacity.jointLaw_toMeasure
attribute [local simp] ChannelCapacity.outputPrior_toMeasure
attribute [local simp] ProbabilityMeasure.convexCombination_toMeasure



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open ChannelCapacity
open InformationTheory
namespace ChannelCapacity
theorem _root_.solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [StandardBorelSpace α] [Nonempty α]
    (k : Kernel α β) [IsMarkovKernel k] (p : ProbabilityMeasure α) (ν : Measure β)
    [IsFiniteMeasure ν] :
    klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν) =
      klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure +
        klDiv (outputPrior k p).toMeasure ν := by
  let e : (α × β) ≃ᵐ (β × α) := MeasurableEquiv.prodComm
  let post : Kernel β α := k†p.toMeasure
  have hce : ⇑(MeasurableEquiv.prodComm : (α × β) ≃ᵐ (β × α)) = Prod.swap := rfl
  have hswap_joint :
      ((jointLaw k p).toMeasure).map e = (outputPrior k p).toMeasure ⊗ₘ post := by
    simpa [jointLaw_toMeasure, outputPrior_toMeasure, e, post, hce] using
      (ProbabilityTheory.compProd_posterior_eq_map_swap (κ := k) (μ := p.toMeasure)).symm
  have hswap_const :
      (p.toMeasure ⊗ₘ Kernel.const α ν).map e = ν ⊗ₘ Kernel.const β p.toMeasure := by
    simpa [e, hce] using
      (by
        rw [Measure.compProd_const, Measure.prod_swap, ← Measure.compProd_const] :
          (p.toMeasure ⊗ₘ Kernel.const α ν).map Prod.swap =
            ν ⊗ₘ Kernel.const β p.toMeasure)
  have hswap_indep :
      ((independentJointLaw k p).toMeasure).map e =
        (outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure := by
    simpa [independentJointLaw_toMeasure, e, hce] using
      (by
        rw [independentJointLaw_toMeasure, Measure.compProd_const, Measure.prod_swap,
          ← Measure.compProd_const] :
          (independentJointLaw k p).toMeasure.map Prod.swap =
            (outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure)
  have hleft :
      klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν) =
        klDiv ((outputPrior k p).toMeasure ⊗ₘ post) (ν ⊗ₘ Kernel.const β p.toMeasure) := by
    calc
      klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν) =
          klDiv (((jointLaw k p).toMeasure).map e) ((p.toMeasure ⊗ₘ Kernel.const α ν).map e) := by
            symm
            exact klDiv_map_measurableEquiv e (jointLaw k p).toMeasure
              (p.toMeasure ⊗ₘ Kernel.const α ν)
      _ = klDiv ((outputPrior k p).toMeasure ⊗ₘ post) (ν ⊗ₘ Kernel.const β p.toMeasure) := by
        rw [hswap_joint, hswap_const]
  have hright :
      klDiv ((outputPrior k p).toMeasure ⊗ₘ post)
          ((outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure) =
        klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure := by
    calc
      klDiv ((outputPrior k p).toMeasure ⊗ₘ post)
          ((outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure) =
          klDiv (((jointLaw k p).toMeasure).map e)
            (((independentJointLaw k p).toMeasure).map e) := by
            rw [hswap_joint, hswap_indep]
      _ = klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure := by
        exact klDiv_map_measurableEquiv e (jointLaw k p).toMeasure
          (independentJointLaw k p).toMeasure
  calc
    klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν) =
        klDiv ((outputPrior k p).toMeasure ⊗ₘ post) (ν ⊗ₘ Kernel.const β p.toMeasure) := hleft
    _ = klDiv (outputPrior k p).toMeasure ν +
          klDiv ((outputPrior k p).toMeasure ⊗ₘ post)
            ((outputPrior k p).toMeasure ⊗ₘ Kernel.const β p.toMeasure) := by
          rw [InformationTheory.klDiv_compProd_eq_add]
    _ = klDiv (outputPrior k p).toMeasure ν +
          klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure := by
          rw [hright]
    _ = klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure +
          klDiv (outputPrior k p).toMeasure ν := by
          rw [add_comm]
end ChannelCapacity
