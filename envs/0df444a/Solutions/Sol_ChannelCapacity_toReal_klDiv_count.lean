-- Prove2me | solution 1 for ChannelCapacity.toReal_klDiv_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:22.599179+00:00
-- url     : https://prove2.me/submissions/f72cb2bb-3330-4bd4-a0ae-03cbe2be2fc7

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Finite
public import Theorems.Thm_ChannelCapacity_toMeasure_eq_count_withDensity
public import Theorems.Thm_ChannelCapacity_rnDeriv_count_ae
public import Theorems.Thm_ChannelCapacity_klFun_singletonMass
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
public import Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_dirac
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_id
attribute [local simp] ChannelCapacity.independentJointLaw_toMeasure
attribute [local simp] ChannelCapacity.jointLaw_toMeasure
attribute [local simp] ChannelCapacity.outputPrior_toMeasure
attribute [local simp] ProbabilityMeasure.convexCombination_toMeasure



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
namespace ChannelCapacity
theorem _root_.solution (μ : ProbabilityMeasure α) :
    (InformationTheory.klDiv μ.toMeasure Measure.count).toReal =
      (Fintype.card α : ℝ) - 1 - ProbabilityMeasure.entropy μ := by
  let _instCountable : Countable α := by infer_instance
  have h_ac : μ.toMeasure ≪ Measure.count := by
    rw [toMeasure_eq_count_withDensity (μ := μ)]
    exact withDensity_absolutelyContinuous _ _
  have h_rn : ∀ a : α, μ.toMeasure.rnDeriv Measure.count a = μ.toMeasure {a} := by
    simpa using (Measure.ae_count_iff.mp (rnDeriv_count_ae (μ := μ)))
  rw [InformationTheory.toReal_klDiv_eq_integral_klFun h_ac, MeasureTheory.integral_count]
  simp_rw [h_rn, klFun_singletonMass (μ := μ)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hprob_enn : ∑ a, μ.toMeasure {a} = (1 : ℝ≥0∞) := by
    calc
      ∑ a, μ.toMeasure {a} = ∑' a : α, μ.toMeasure {a} := by
        rw [← tsum_fintype
          (L := SummationFilter.unconditional _)
          (f := fun a : α => μ.toMeasure {a})]
      _ = μ.toMeasure Set.univ := by
        simpa only [Set.indicator_univ] using
          μ.toMeasure.tsum_indicator_apply_singleton Set.univ MeasurableSet.univ
      _ = 1 := by exact μ.prop.measure_univ
  have hprob : ∑ a, (μ.toMeasure {a}).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ha => measure_ne_top _ _), hprob_enn, ENNReal.toReal_one]
  rw [ProbabilityMeasure.entropy, hprob, Finset.card_univ]
  ring
end ChannelCapacity
