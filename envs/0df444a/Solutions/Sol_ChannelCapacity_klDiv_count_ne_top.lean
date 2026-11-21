-- Prove2me | solution 1 for ChannelCapacity.klDiv_count_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:33.821017+00:00
-- url     : https://prove2.me/submissions/2bd3d0db-fb38-4def-b648-81204869deb4

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_absolutelyContinuous_count

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
omit [Fintype β]
namespace ChannelCapacity
theorem _root_.solution (μ : ProbabilityMeasure β) [Finite β] :
    InformationTheory.klDiv μ.toMeasure Measure.count ≠ ∞ := by
  let _instFintypeβ : Fintype β := Fintype.ofFinite β
  let _instCountableβ : Countable β := by infer_instance
  have h_ac : μ.toMeasure ≪ Measure.count := absolutelyContinuous_count μ
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac h_ac, MeasureTheory.lintegral_count,
    tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top
end ChannelCapacity
