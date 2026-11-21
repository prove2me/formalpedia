-- Prove2me | solution 1 for ChannelCapacity.Kernel.mutualInformation_strictlyConcave_of_injectivePriorPushforward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:09.161411+00:00
-- url     : https://prove2.me/submissions/54366796-729a-40e4-b371-9e41b3b83149

module
public import Definitions.Def_LeanPool_ChannelCapacity_NonDegeneracy
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_StrictConcavity
public import Theorems.Thm_ProbabilityMeasure_convexCombination_ne_left
public import Theorems.Thm_ProbabilityMeasure_convexCombination_ne_right
public import Theorems.Thm_ChannelCapacity_Kernel_outputMarginalReference_self
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_dirac
public import Theorems.Thm_ChannelCapacity_Kernel_priorPushforward_id
public import Theorems.Thm_ChannelCapacity_independentJointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_jointLaw_toMeasure
public import Theorems.Thm_ChannelCapacity_outputPrior_toMeasure
public import Theorems.Thm_ProbabilityMeasure_convexCombination_toMeasure
public import Theorems.Thm_ProbabilityTheory_klDiv_compProd_right
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_dirac
attribute [local simp] ChannelCapacity.Kernel.priorPushforward_id
attribute [local simp] ChannelCapacity.independentJointLaw_toMeasure
attribute [local simp] ChannelCapacity.jointLaw_toMeasure
attribute [local simp] ChannelCapacity.outputPrior_toMeasure
attribute [local simp] ProbabilityMeasure.convexCombination_toMeasure


section
@[expose] public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
namespace ProbabilityMeasure
variable {α : Type*} [MeasurableSpace α]
end ProbabilityMeasure
namespace ChannelCapacity
open ProbabilityMeasure
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
namespace Kernel
private lemma mutualInformation_strictlyConcave_aux
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (k : Kernel α β) [IsMarkovKernel k]
    (h : Kernel.InjectivePriorPushforward k)
    (hWC : Kernel.WellConditionedForCapacity k)
    (p q : ProbabilityMeasure α) (h_ne : p ≠ q) (t : NNReal)
    (ht_pos : 0 < t) (ht_lt_one : t < 1) :
    mutualInformation (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) k >
      (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k := by
  let r := ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)
  let ν := (outputPrior k r).toMeasure
  let Kp :=
    InformationTheory.klDiv (jointLaw k p).toMeasure (p.toMeasure ⊗ₘ Kernel.const α ν)
  let Kq :=
    InformationTheory.klDiv (jointLaw k q).toMeasure (q.toMeasure ⊗ₘ Kernel.const α ν)
  let Kr :=
    InformationTheory.klDiv (jointLaw k r).toMeasure (r.toMeasure ⊗ₘ Kernel.const α ν)
  let Dp := InformationTheory.klDiv (outputPrior k p).toMeasure ν
  let Dq := InformationTheory.klDiv (outputPrior k q).toMeasure ν
  have ht_ne_zero : (t : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt ht_pos)
  have hs_pos : 0 < (1 : NNReal) - t := by
    exact tsub_pos_iff_lt.mpr ht_lt_one
  have hs_ne_zero : ((((1 : NNReal) - t : NNReal) : ENNReal)) ≠ 0 := by
    exact_mod_cast (ne_of_gt hs_pos)
  have hp_ac_r : p.toMeasure ≪ r.toMeasure := by
    refine (Measure.absolutelyContinuous_smul ht_ne_zero).trans ?_
    dsimp [r]
    simpa using
      (Measure.absolutelyContinuous_of_le
        (μ := t • p.toMeasure)
        (ν := t • p.toMeasure + ((1 : NNReal) - t) • q.toMeasure)
        (le_add_of_nonneg_right bot_le))
  have hq_ac_r : q.toMeasure ≪ r.toMeasure := by
    refine (Measure.absolutelyContinuous_smul hs_ne_zero).trans ?_
    dsimp [r]
    simpa using
      (Measure.absolutelyContinuous_of_le
        (μ := ((1 : NNReal) - t) • q.toMeasure)
        (ν := t • p.toMeasure + ((1 : NNReal) - t) • q.toMeasure)
        (le_add_of_nonneg_left bot_le))
  have hr_rows : ∀ᵐ x ∂r.toMeasure, k x ≪ ν := by
    simpa [ν] using hWC.hRowAC r
  have hp_rows : ∀ᵐ x ∂p.toMeasure, k x ≪ ν := by
    rw [ae_iff]
    exact hp_ac_r (by simpa [ae_iff] using hr_rows)
  have hq_rows : ∀ᵐ x ∂q.toMeasure, k x ≪ ν := by
    rw [ae_iff]
    exact hq_ac_r (by simpa [ae_iff] using hr_rows)
  have hKp_eq :
      Kp = ∫⁻ x, InformationTheory.klDiv (k x) ν ∂p.toMeasure := by
    apply klDiv_compProd_right
    exact Measure.AbsolutelyContinuous.compProd_right hp_rows
  have hKq_eq :
      Kq = ∫⁻ x, InformationTheory.klDiv (k x) ν ∂q.toMeasure := by
    apply klDiv_compProd_right
    exact Measure.AbsolutelyContinuous.compProd_right hq_rows
  have hKr_eq :
      Kr = ∫⁻ x, InformationTheory.klDiv (k x) ν ∂r.toMeasure := by
    apply klDiv_compProd_right
    exact Measure.AbsolutelyContinuous.compProd_right hr_rows
  have hν_ref_p : Kernel.OutputMarginalReference k p ν := by
    exact ⟨r, hp_ac_r, rfl⟩
  have hν_ref_q : Kernel.OutputMarginalReference k q ν := by
    exact ⟨r, hq_ac_r, rfl⟩
  have hν_ref_r : Kernel.OutputMarginalReference k r ν := by
    exact Kernel.outputMarginalReference_self k r
  have hKp_fin : Kp ≠ ∞ := hWC.hFiniteRefKL p ν hν_ref_p
  have hKq_fin : Kq ≠ ∞ := hWC.hFiniteRefKL q ν hν_ref_q
  have hKr_fin : Kr ≠ ∞ := hWC.hFiniteRefKL r ν hν_ref_r
  have hMIp_fin :
      InformationTheory.klDiv (jointLaw k p).toMeasure (independentJointLaw k p).toMeasure ≠ ∞ := by
    simpa [independentJointLaw_toMeasure] using
      hWC.hFiniteRefKL p (outputPrior k p).toMeasure
        (Kernel.outputMarginalReference_self k p)
  have hMIq_fin :
      InformationTheory.klDiv (jointLaw k q).toMeasure (independentJointLaw k q).toMeasure ≠ ∞ := by
    simpa [independentJointLaw_toMeasure] using
      hWC.hFiniteRefKL q (outputPrior k q).toMeasure
        (Kernel.outputMarginalReference_self k q)
  have hMIr_fin :
      InformationTheory.klDiv (jointLaw k r).toMeasure (independentJointLaw k r).toMeasure ≠ ∞ := by
    simpa [independentJointLaw_toMeasure] using
      hWC.hFiniteRefKL r (outputPrior k r).toMeasure
        (Kernel.outputMarginalReference_self k r)
  have hChain_p :
      Kp =
        InformationTheory.klDiv
            (jointLaw k p).toMeasure
            (independentJointLaw k p).toMeasure +
          Dp := by
    simpa [Kp, Dp] using hWC.hChainRule p ν hν_ref_p
  have hChain_q :
      Kq =
        InformationTheory.klDiv
            (jointLaw k q).toMeasure
            (independentJointLaw k q).toMeasure +
          Dq := by
    simpa [Kq, Dq] using hWC.hChainRule q ν hν_ref_q
  have hChain_r :
      Kr =
        InformationTheory.klDiv (jointLaw k r).toMeasure (independentJointLaw k r).toMeasure +
          InformationTheory.klDiv (outputPrior k r).toMeasure ν := by
    simpa [Kr] using hWC.hChainRule r ν hν_ref_r
  have hDp_fin : Dp ≠ ∞ := by
    intro hDp_top
    have : Kp = ∞ := by
      rw [hChain_p, hDp_top, add_top]
    exact hKp_fin this
  have hDq_fin : Dq ≠ ∞ := by
    intro hDq_top
    have : Kq = ∞ := by
      rw [hChain_q, hDq_top, add_top]
    exact hKq_fin this
  have hKr_real :
      Kr.toReal = (t : ℝ) * Kp.toReal + (1 - (t : ℝ)) * Kq.toReal := by
    have hr_toMeasure :
        r.toMeasure = t • p.toMeasure + ((1 : NNReal) - t) • q.toMeasure := by
      simp [r, ProbabilityMeasure.convexCombination_toMeasure]
    have hleft_fin :
        t • ∫⁻ x, InformationTheory.klDiv (k x) ν ∂p.toMeasure ≠ ∞ := by
      rw [← hKp_eq]
      simpa [ENNReal.smul_def, smul_eq_mul] using ENNReal.mul_ne_top (by simp) hKp_fin
    have hright_fin :
        ((1 : NNReal) - t) • ∫⁻ x, InformationTheory.klDiv (k x) ν ∂q.toMeasure ≠ ∞ := by
      rw [← hKq_eq]
      have hcoeff : ((((1 : NNReal) - t : NNReal) : ENNReal)) ≠ ∞ := by simp
      simpa [ENNReal.smul_def, smul_eq_mul] using ENNReal.mul_ne_top hcoeff hKq_fin
    rw [hKr_eq, hKp_eq, hKq_eq]
    rw [hr_toMeasure]
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      ENNReal.toReal_add hleft_fin hright_fin, ENNReal.toReal_smul, ENNReal.toReal_smul]
    simp [NNReal.smul_def, NNReal.coe_sub (le_of_lt ht_lt_one), sub_eq_add_neg]
  have hKp_real :
      Kp.toReal = mutualInformation p k + Dp.toReal := by
    rw [hChain_p, ENNReal.toReal_add hMIp_fin hDp_fin, mutualInformation]
  have hKq_real :
      Kq.toReal = mutualInformation q k + Dq.toReal := by
    rw [hChain_q, ENNReal.toReal_add hMIq_fin hDq_fin, mutualInformation]
  have hKr_real' : Kr.toReal = mutualInformation r k := by
    have hOutSelf : InformationTheory.klDiv (outputPrior k r).toMeasure ν = 0 := by simp [ν]
    calc
      Kr.toReal =
          (InformationTheory.klDiv (jointLaw k r).toMeasure (independentJointLaw k r).toMeasure +
            0).toReal := by rw [hChain_r, hOutSelf]
      _ =
          (InformationTheory.klDiv
              (jointLaw k r).toMeasure
              (independentJointLaw k r).toMeasure).toReal +
            0 := by simp
      _ = mutualInformation r k := by simp [mutualInformation]
  have hr_ne_p : r ≠ p := ProbabilityMeasure.convexCombination_ne_left h_ne ht_lt_one
  have hr_ne_q : r ≠ q := ProbabilityMeasure.convexCombination_ne_right h_ne ht_pos ht_lt_one
  have hOutp_ne : outputPrior k p ≠ outputPrior k r := by
    intro h_eq
    exact hr_ne_p ((h <| by simpa [Kernel.priorPushforward] using h_eq).symm)
  have hOutq_ne : outputPrior k q ≠ outputPrior k r := by
    intro h_eq
    exact hr_ne_q ((h <| by simpa [Kernel.priorPushforward] using h_eq).symm)
  have hDp_ne_zero : Dp ≠ 0 := by
    intro hDp_zero
    exact hOutp_ne <| ProbabilityMeasure.toMeasure_injective
      ((InformationTheory.klDiv_eq_zero_iff).mp hDp_zero)
  have hDq_ne_zero : Dq ≠ 0 := by
    intro hDq_zero
    exact hOutq_ne <| ProbabilityMeasure.toMeasure_injective
      ((InformationTheory.klDiv_eq_zero_iff).mp hDq_zero)
  have hDp_pos : 0 < Dp.toReal := ENNReal.toReal_pos hDp_ne_zero hDp_fin
  have hDq_pos : 0 < Dq.toReal := ENNReal.toReal_pos hDq_ne_zero hDq_fin
  have hExtra_pos :
      0 < (t : ℝ) * Dp.toReal + (1 - (t : ℝ)) * Dq.toReal := by
    have ht_real : 0 < (t : ℝ) := by exact_mod_cast ht_pos
    have hs_real : 0 < 1 - (t : ℝ) := by
      linarith [show (t : ℝ) < 1 by exact_mod_cast ht_lt_one]
    nlinarith [hDp_pos, hDq_pos, ht_real, hs_real]
  calc
    mutualInformation r k = Kr.toReal := hKr_real'.symm
    _ = (t : ℝ) * Kp.toReal + (1 - (t : ℝ)) * Kq.toReal := hKr_real
    _ = (t : ℝ) * (mutualInformation p k + Dp.toReal) +
          (1 - (t : ℝ)) * (mutualInformation q k + Dq.toReal) := by
          rw [hKp_real, hKq_real]
    _ = (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k +
          ((t : ℝ) * Dp.toReal + (1 - (t : ℝ)) * Dq.toReal) := by ring
    _ > (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k := by
      linarith
end Kernel
end ChannelCapacity
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal
open ChannelCapacity
open ProbabilityMeasure
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
open ChannelCapacity.Kernel
namespace ChannelCapacity.Kernel
theorem _root_.solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (k : Kernel α β) [IsMarkovKernel k]
    (h : Kernel.InjectivePriorPushforward k)
    (hWC : Kernel.WellConditionedForCapacity k) :
    ∀ (p q : ProbabilityMeasure α) (_h_ne : p ≠ q) (t : NNReal)
      (_ht_pos : 0 < t) (ht_lt_one : t < 1),
      mutualInformation (ProbabilityMeasure.convexCombination p q t (le_of_lt ht_lt_one)) k >
        (t : ℝ) * mutualInformation p k + (1 - (t : ℝ)) * mutualInformation q k := by
  intro p q h_ne t ht_pos ht_lt_one
  simpa using mutualInformation_strictlyConcave_aux k h hWC p q h_ne t ht_pos ht_lt_one
end ChannelCapacity.Kernel
