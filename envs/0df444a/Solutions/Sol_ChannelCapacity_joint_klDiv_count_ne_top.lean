-- Prove2me | solution 1 for ChannelCapacity.joint_klDiv_count_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:30.848403+00:00
-- url     : https://prove2.me/submissions/0a12f0ea-4d27-4d2d-8597-75e771697841

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_absolutelyContinuous_count
public import Theorems.Thm_ChannelCapacity_klDiv_count_ne_top
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ProbabilityTheory_klDiv_compProd_right
attribute [local simp] ChannelCapacity.jointLaw_toMeasure



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
omit [Fintype α] [Fintype β]
namespace ChannelCapacity
theorem _root_.solution (k : Kernel α β) [IsMarkovKernel k] [Finite α] [Finite β]
    (p : ProbabilityMeasure α) :
    InformationTheory.klDiv
        (jointLaw k p).toMeasure
        (p.toMeasure ⊗ₘ Kernel.const α Measure.count) ≠ ∞ := by
  let _instFintypeα : Fintype α := Fintype.ofFinite α
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  let _instCountableα : Countable α := by infer_instance
  let _instCountableβ : Countable β := by infer_instance
  have h_rows : ∀ᵐ a ∂p.toMeasure, k a ≪ Measure.count := by
    exact ae_of_all _ fun a => absolutelyContinuous_count (Kernel.rowProbabilityMeasure k a)
  have h_kl :
      InformationTheory.klDiv
          (jointLaw k p).toMeasure
          (p.toMeasure ⊗ₘ Kernel.const α Measure.count) =
        ∫⁻ a, InformationTheory.klDiv (k a) Measure.count ∂p.toMeasure := by
    rw [jointLaw_toMeasure]
    apply ProbabilityTheory.klDiv_compProd_right
    exact Measure.AbsolutelyContinuous.compProd_right h_rows
  rw [h_kl, MeasureTheory.lintegral_fintype]
  exact ENNReal.sum_ne_top.2 fun a _ha =>
    ENNReal.mul_ne_top
      (klDiv_count_ne_top (Kernel.rowProbabilityMeasure k a))
      (measure_ne_top _ _)
end ChannelCapacity
