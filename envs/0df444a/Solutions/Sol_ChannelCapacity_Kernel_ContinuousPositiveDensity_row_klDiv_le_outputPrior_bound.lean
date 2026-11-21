-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.row_klDiv_le_outputPrior_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:47.443989+00:00
-- url     : https://prove2.me/submissions/3525c485-7c44-4ef9-8fbf-4864c65895e2

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_row_eq_withDensity
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_exists_uniform_density_bounds
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_klFun_le_sq_add_one
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_aemeasurable_outputDensity
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_outputPrior_eq_withDensity_outputDensity
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_outputDensity_pos
public import Theorems.Thm_ChannelCapacity_Kernel_ContinuousPositiveDensity_row_absolutelyContinuous_outputPrior
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
open scoped ENNReal
open ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [TopologicalSpace α] [TopologicalSpace β]
open ChannelCapacity.Kernel
open ChannelCapacity.Kernel.ContinuousPositiveDensity
variable {k : Kernel α β} [IsMarkovKernel k] [OpensMeasurableSpace α] {ν : Measure β}
variable [CompactSpace α] [CompactSpace β] [PolishSpace α] [PolishSpace β]
variable [BorelSpace α] [BorelSpace β]
variable [OpensMeasurableSpace β] [IsFiniteMeasure ν]
omit [BorelSpace α] [BorelSpace β]
namespace ChannelCapacity.Kernel.ContinuousPositiveDensity
theorem _root_.solution
    (h : ContinuousPositiveDensity k ν) (p : ProbabilityMeasure α) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧
      ∀ a : α, InformationTheory.klDiv (k a) (outputPrior k p).toMeasure ≤ B := by
  let : Nonempty α := p.nonempty
  let : Nonempty β := (outputPrior k p).nonempty
  rcases h.exists_uniform_density_bounds with ⟨c, C, hc_pos, h_bounds⟩
  let Breal : ℝ := (((c : ENNReal)⁻¹ * (C : ENNReal)).toReal) ^ 2 + 1
  let B : ℝ≥0∞ := ENNReal.ofReal Breal
  refine ⟨B, by simp [B], ?_⟩
  intro a
  have h_out_lower : ∀ b, (c : ENNReal) ≤ h.outputDensity p b := by
    intro b
    have h_c_le_density : ∀ a' : α, (c : ENNReal) ≤ (h.density a' b : ENNReal) := by
      intro a'
      exact_mod_cast (h_bounds a' b).1
    calc
      (c : ENNReal) = ∫⁻ a', (c : ENNReal) ∂p.toMeasure := by simp
      _ ≤ ∫⁻ a', (h.density a' b : ENNReal) ∂p.toMeasure := by
        exact lintegral_mono h_c_le_density
      _ = h.outputDensity p b := rfl
  have h_out_upper : ∀ b, h.outputDensity p b ≤ (C : ENNReal) := by
    intro b
    have h_density_le_C : ∀ a' : α, (h.density a' b : ENNReal) ≤ (C : ENNReal) := by
      intro a'
      exact_mod_cast (h_bounds a' b).2
    calc
      h.outputDensity p b = ∫⁻ a', (h.density a' b : ENNReal) ∂p.toMeasure := rfl
      _ ≤ ∫⁻ a', (C : ENNReal) ∂p.toMeasure := by
        exact lintegral_mono h_density_le_C
      _ = (C : ENNReal) := by simp
  have h_out_ne_top : ∀ b, h.outputDensity p b ≠ ∞ := by
    intro b
    exact ne_top_of_le_ne_top (by simp) (h_out_upper b)
  have h_ac : k a ≪ (outputPrior k p).toMeasure :=
    h.row_absolutelyContinuous_outputPrior p a
  have h_out_ac_ref :
      (outputPrior k p).toMeasure ≪ ν := by
    simpa [h.outputPrior_eq_withDensity_outputDensity p] using
      MeasureTheory.withDensity_absolutelyContinuous ν (h.outputDensity p)
  have hmeas_density_a : Measurable (fun b => (h.density a b : ENNReal)) := by
    have hcont_density_a : Continuous fun b : β => h.density a b := by
      have hpair : Continuous fun b : β => (a, b) := by
        fun_prop
      exact h.continuous_density.comp hpair
    exact (ENNReal.continuous_coe.comp hcont_density_a).measurable
  have h_rnDeriv_ref :
      (k a).rnDeriv ν =ᵐ[ν] fun b => (h.density a b : ENNReal) := by
    rw [h.row_eq_withDensity a]
    exact Measure.rnDeriv_withDensity ν hmeas_density_a
  have h_rnDeriv_withDensity :
      (k a).rnDeriv (ν.withDensity (h.outputDensity p)) =ᵐ[ν]
        fun b => (h.outputDensity p b)⁻¹ * ((k a).rnDeriv ν b) := by
    exact Measure.rnDeriv_withDensity_right
      (μ := k a) (ν := ν) (f := h.outputDensity p)
      (h.aemeasurable_outputDensity p)
      (Filter.Eventually.of_forall fun b => (h.outputDensity_pos p b).ne')
      (Filter.Eventually.of_forall fun b => h_out_ne_top b)
  have h_rnDeriv_out_ν :
      (k a).rnDeriv ((outputPrior k p).toMeasure) =ᵐ[ν]
        fun b => (h.outputDensity p b)⁻¹ * (h.density a b : ENNReal) := by
    filter_upwards [h_rnDeriv_withDensity, h_rnDeriv_ref] with b hb hb'
    simpa [h.outputPrior_eq_withDensity_outputDensity p, hb'] using hb
  have h_rnDeriv_out :
      (k a).rnDeriv ((outputPrior k p).toMeasure) =ᵐ[(outputPrior k p).toMeasure]
        fun b => (h.outputDensity p b)⁻¹ * (h.density a b : ENNReal) := by
    exact h_out_ac_ref.ae_eq h_rnDeriv_out_ν
  have h_integrand_le :
      ∀ᵐ b ∂(outputPrior k p).toMeasure,
        ENNReal.ofReal
            (InformationTheory.klFun
              (((k a).rnDeriv ((outputPrior k p).toMeasure) b).toReal)) ≤
          B := by
    filter_upwards [h_rnDeriv_out] with b hb
    have h_density_le_C : (h.density a b : ENNReal) ≤ (C : ENNReal) := by
      exact_mod_cast (h_bounds a b).2
    have hratio_le :
        (h.outputDensity p b)⁻¹ * (h.density a b : ENNReal) ≤
          (c : ENNReal)⁻¹ * (C : ENNReal) := by
      calc
        (h.outputDensity p b)⁻¹ * (h.density a b : ENNReal) ≤
            (c : ENNReal)⁻¹ * (h.density a b : ENNReal) := by
              gcongr
              exact h_out_lower b
        _ ≤ (c : ENNReal)⁻¹ * (C : ENNReal) := by
              gcongr
    have hratio_real_le :
        (((h.outputDensity p b)⁻¹ * (h.density a b : ENNReal)).toReal) ≤
          (((c : ENNReal)⁻¹ * (C : ENNReal)).toReal) := by
      have hbound_ne_top : ((c : ENNReal)⁻¹ * (C : ENNReal)) ≠ ∞ := by
        refine ENNReal.mul_ne_top ?_ ?_
        · simp [hc_pos.ne']
        · simp
      exact ENNReal.toReal_mono hbound_ne_top hratio_le
    have hkl_le :
        InformationTheory.klFun
            (((h.outputDensity p b)⁻¹ * (h.density a b : ENNReal)).toReal) ≤
          Breal := by
      exact klFun_le_sq_add_one ENNReal.toReal_nonneg hratio_real_le
    have hkl_le' :
        InformationTheory.klFun
            ((((k a).rnDeriv ((outputPrior k p).toMeasure)) b).toReal) ≤
          Breal := by
      rw [hb]
      simpa [ENNReal.toReal_mul, h_out_ne_top b, ENNReal.toReal_inv,
        (h.outputDensity_pos p b).ne'] using hkl_le
    exact ENNReal.ofReal_le_ofReal hkl_le'
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac h_ac]
  calc
    ∫⁻ b,
        ENNReal.ofReal
          (InformationTheory.klFun (((k a).rnDeriv ((outputPrior k p).toMeasure) b).toReal)) ∂
        (outputPrior k p).toMeasure ≤
      ∫⁻ _, B ∂(outputPrior k p).toMeasure := by
        exact lintegral_mono_ae h_integrand_le
    _ = B := by simp [B]
end ChannelCapacity.Kernel.ContinuousPositiveDensity
