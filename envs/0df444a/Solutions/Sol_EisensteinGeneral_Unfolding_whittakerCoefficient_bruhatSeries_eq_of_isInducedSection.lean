-- Prove2me | solution 1 for EisensteinGeneral.Unfolding.whittakerCoefficient_bruhatSeries_eq_of_isInducedSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/3dd71bfc-f2f6-551c-b9f1-8d79faf4262c

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinGeneral_Unfolding_whittakerCoefficient_bruhatSeries_eq_of_isInducedSection

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicHaar IsDedekindDomain AutomorphicForm
open ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace WhittakerUnfolding

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private theorem addChar_neg_algebraMap_mul_ne_one
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) {α : F} (hα : α ≠ 0) :
    ∃ y : AdeleRing (𝓞 F) F, ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * y)) ≠ 1 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ψ x₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ.nontrivial (DFunLike.ext _ _ fun x => by rw [h x, AddChar.one_apply])
  refine ⟨algebraMap F (AdeleRing (𝓞 F) F) (-α⁻¹) * x₀, ?_⟩
  have key : -(algebraMap F (AdeleRing (𝓞 F) F) α *
      (algebraMap F (AdeleRing (𝓞 F) F) (-α⁻¹) * x₀)) = x₀ := by
    rw [← mul_assoc, ← map_mul, mul_neg, mul_inv_cancel₀ hα, map_neg, map_one, neg_one_mul,
      neg_neg]
  rw [key]; exact hx₀

private scoped instance : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  have hsurj : Function.Surjective
      (fun β : F => (⟨algebraMap F _ β, β, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F)) := by
    rintro ⟨_, β, rfl⟩; exact ⟨β, rfl⟩
  exact hsurj.countable

private theorem addChar_neg_algebraMap_mul_vadd_invariant
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) (α : F) :
    ∀ (γ : AdeleRing.principalSubgroup (𝓞 F) F) (x : AdeleRing (𝓞 F) F),
      ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * (γ +ᵥ x))) =
      ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) := by
  rintro ⟨_, β, rfl⟩ x
  have hv : ((⟨algebraMap F _ β, β, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F) +ᵥ x)
      = algebraMap F (AdeleRing (𝓞 F) F) β + x := rfl
  rw [hv, mul_add, neg_add, ψ.map_add_eq_mul]
  have h1 : ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α *
      algebraMap F (AdeleRing (𝓞 F) F) β)) = 1 := by
    rw [← map_mul, ← map_neg]
    exact hψ.principalInvariant (-(α * β))
  rw [h1, one_mul]

private theorem setIntegral_adelicBox_addChar_neg_algebraMap_mul
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) {α : F} (hα : α ≠ 0) :
    ∫ x in adelicBox F, ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
      ∂(adelicAddHaar (𝓞 F) F) = 0 := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  set μ := adelicAddHaar (𝓞 F) F with hμ
  set α𝔸 := algebraMap F (AdeleRing (𝓞 F) F) α
  set f : AdeleRing (𝓞 F) F → ℂ := fun x => ψ (-(α𝔸 * x)) with hf
  obtain ⟨y₀, hy₀⟩ := addChar_neg_algebraMap_mul_ne_one F ψ hψ hα
  set c : ℂ := ψ (-(α𝔸 * y₀)) with hc
  have hFD_B : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) (adelicBox F) μ :=
    isAddFundamentalDomain_adelicBox_adelicAddHaar F
  have hFD_shift :
      IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
        ((Equiv.addLeft y₀) '' adelicBox F) μ := by
    refine hFD_B.image_of_equiv (Equiv.addLeft y₀)
      (measurePreserving_add_left μ (-y₀)).quasiMeasurePreserving (Equiv.refl _) ?_
    intro γ x
    simp only [Equiv.coe_addLeft, Equiv.refl_apply, AddSubgroup.vadd_def]
    exact (add_left_comm _ _ _).symm
  have hf_periodic := addChar_neg_algebraMap_mul_vadd_invariant F ψ hψ α
  have step1 : ∫ x in adelicBox F, f x ∂μ =
      ∫ x in (Equiv.addLeft y₀) '' adelicBox F, f x ∂μ :=
    hFD_B.setIntegral_eq hFD_shift hf_periodic
  have step2 : ∫ x in (Equiv.addLeft y₀) '' adelicBox F, f x ∂μ
      = c * ∫ x in adelicBox F, f x ∂μ := by
    have hmp : MeasurePreserving (fun x => y₀ + x) μ μ := measurePreserving_add_left μ y₀
    have hemb : MeasurableEmbedding (fun x : AdeleRing (𝓞 F) F => y₀ + x) :=
      (Homeomorph.addLeft y₀).measurableEmbedding
    have heq : (Equiv.addLeft y₀) '' adelicBox F = (fun x => y₀ + x) '' adelicBox F := rfl
    rw [heq, hmp.setIntegral_image_emb hemb f (adelicBox F)]
    have hsplit : ∀ x, f (y₀ + x) = c * f x := fun x => by
      simp only [hf, hc, α𝔸, mul_add, neg_add, ψ.map_add_eq_mul]
    simp_rw [hsplit]
    exact integral_const_mul c _
  have hI := step1.trans step2
  have h1c : (1 - c) * ∫ x in adelicBox F, f x ∂μ = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact hI
  exact (mul_eq_zero.mp h1c).resolve_left (sub_ne_zero.mpr hy₀.symm)

private scoped instance : Nontrivial (AdeleRing (𝓞 F) F) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact ⟨⟨0, 1, fun h => zero_ne_one (α := w.Completion) (congrArg (fun z : AdeleRing (𝓞 F) F => z.1 w) h)⟩⟩

private def principalEquiv : F ≃ AdeleRing.principalSubgroup (𝓞 F) F :=
  Equiv.ofBijective (fun β => ⟨algebraMap F _ β, β, rfl⟩)
    ⟨fun a b h => (algebraMap F (AdeleRing (𝓞 F) F)).injective (congrArg Subtype.val h),
     by rintro ⟨_, β, rfl⟩; exact ⟨β, rfl⟩⟩

private theorem principalEquiv_vadd (β : F) (x : AdeleRing (𝓞 F) F) :
    (principalEquiv F β) +ᵥ x = algebraMap F (AdeleRing (𝓞 F) F) β + x := rfl

private theorem integrable_tsum_of_lintegral {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Countable ι]
    {f : ι → X → ℂ} (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hf' : ∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ ≠ ∞) :
    Integrable (fun a => ∑' i, f i a) μ := by
  have hf'' : ∀ i, AEMeasurable (fun a => ‖f i a‖ₑ) μ := fun i => (hf i).enorm
  have hhh : ∀ᵐ a ∂μ, Summable fun n => (‖f n a‖₊ : ℝ) := by
    rw [← lintegral_tsum hf''] at hf'
    refine (ae_lt_top' (AEMeasurable.tsum hf'') hf').mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  refine ⟨?_, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
      (fun s => Finset.aestronglyMeasurable_fun_sum s fun i _ => hf i) ?_
    filter_upwards [hhh] with a ha
    exact (ha.of_norm).hasSum
  · have hlt : ∫⁻ a, ∑' n, ‖f n a‖ₑ ∂μ < ∞ := by rwa [lintegral_tsum hf'', lt_top_iff_ne_top]
    exact lt_of_le_of_lt (lintegral_mono fun a => enorm_tsum_le_tsum_enorm) hlt

variable (h : AdeleRing (𝓞 F) F → ℂ)

private theorem integral_eq_tsum_setIntegral_adelicBox (hh : Integrable h (adelicAddHaar (𝓞 F) F)) :
    ∫ y, h y ∂(adelicAddHaar (𝓞 F) F)
      = ∑' ξ : F, ∫ x in adelicBox F, h (algebraMap F (AdeleRing (𝓞 F) F) ξ + x) ∂(adelicAddHaar (𝓞 F) F) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  rw [(isAddFundamentalDomain_adelicBox_adelicAddHaar F).integral_eq_tsum'' h hh]
  exact ((principalEquiv F).tsum_eq fun γ =>
    ∫ x in adelicBox F, h (γ +ᵥ x) ∂(adelicAddHaar (𝓞 F) F)).symm

private theorem tsum_lintegral_adelicBox_translate_eq :
    ∑' ξ : F, ∫⁻ x in adelicBox F, ‖h (algebraMap F (AdeleRing (𝓞 F) F) ξ + x)‖ₑ ∂(adelicAddHaar (𝓞 F) F)
      = ∫⁻ y, ‖h y‖ₑ ∂(adelicAddHaar (𝓞 F) F) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  rw [(isAddFundamentalDomain_adelicBox_adelicAddHaar F).lintegral_eq_tsum'' fun y => ‖h y‖ₑ]
  exact (principalEquiv F).tsum_eq fun γ =>
    ∫⁻ x in adelicBox F, ‖h (γ +ᵥ x)‖ₑ ∂(adelicAddHaar (𝓞 F) F)

private theorem integrableOn_adelicBox_translate (hh : Integrable h (adelicAddHaar (𝓞 F) F)) (ξ : F) :
    IntegrableOn (fun x => h (algebraMap F (AdeleRing (𝓞 F) F) ξ + x)) (adelicBox F) (adelicAddHaar (𝓞 F) F) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  exact (hh.comp_add_left (algebraMap F (AdeleRing (𝓞 F) F) ξ)).integrableOn

private theorem integrableOn_adelicBox_tsum_translate (hh : Integrable h (adelicAddHaar (𝓞 F) F)) :
    IntegrableOn (fun x => ∑' ξ : F, h (algebraMap F (AdeleRing (𝓞 F) F) ξ + x)) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) := by
  refine integrable_tsum_of_lintegral (fun ξ => (integrableOn_adelicBox_translate F h hh ξ).aestronglyMeasurable) ?_
  rw [tsum_lintegral_adelicBox_translate_eq F h]
  exact hh.2.ne

private theorem setIntegral_adelicBox_tsum_translate_eq (hh : Integrable h (adelicAddHaar (𝓞 F) F)) :
    ∫ x in adelicBox F, (∑' ξ : F, h (algebraMap F (AdeleRing (𝓞 F) F) ξ + x)) ∂(adelicAddHaar (𝓞 F) F)
      = ∫ y, h y ∂(adelicAddHaar (𝓞 F) F) := by
  rw [integral_eq_tsum_setIntegral_adelicBox F h hh]
  refine integral_tsum (fun ξ => (integrableOn_adelicBox_translate F h hh ξ).aestronglyMeasurable) ?_
  rw [tsum_lintegral_adelicBox_translate_eq F h]
  exact hh.2.ne

private theorem productionPins_nu :
    (productionPins F).ν = (adelicAddHaar (𝓞 F) F)[|adelicBox F] := rfl

private theorem whittakerCoefficient_productionPins_eq (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPins F) ψ φ α g
      = ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal •
          ∫ x in adelicBox F, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
            ∂(adelicAddHaar (𝓞 F) F) := by
  show (∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
      ∂((adelicAddHaar (𝓞 F) F)[|adelicBox F])) = _
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure]

variable {F}

private def bruhatSeries (φ : AdelicGL2 (𝓞 F) F → ℂ) (g' : AdelicGL2 (𝓞 F) F) : ℂ :=
  φ g' + ∑' ξ' : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')

private def jacquetIntegrand (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (ξ : F)
    (g : AdelicGL2 (𝓞 F) F) (y : AdeleRing (𝓞 F) F) : ℂ :=
  φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y))

private theorem integrable_jacquetIntegrand {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (ξ : F) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    Integrable (jacquetIntegrand ψ φ ξ g) (adelicAddHaar (𝓞 F) F) := by
  refine hint.mul_bdd (c := 1) ?_ ?_
  · exact (hψ.continuous.comp ((continuous_const.mul continuous_id).neg)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => le_of_eq
      (NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ _)

private theorem integrand_eq {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hN : ∀ (x : AdeleRing (𝓞 F) F) (g' : AdelicGL2 (𝓞 F) F), φ (unipotentGL2 x * g') = φ g')
    (ξ : F) (g : AdelicGL2 (𝓞 F) F) (x : AdeleRing (𝓞 F) F) :
    bruhatSeries φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * x))
      = φ g * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * x))
        + ∑' ξ' : F, jacquetIntegrand ψ φ ξ g (algebraMap F (AdeleRing (𝓞 F) F) ξ' + x) := by
  unfold bruhatSeries jacquetIntegrand
  rw [hN, add_mul, ← tsum_mul_right]
  congr 1
  refine tsum_congr fun ξ' => ?_
  have hgrp : adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * (unipotentGL2 x * g)
      = adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ' + x) * g := by
    rw [unipotentGL2_add]; group
  have h1 : ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * algebraMap F (AdeleRing (𝓞 F) F) ξ')) = 1 := by
    rw [← map_mul, ← map_neg]
    exact hψ.principalInvariant (-(ξ * ξ'))
  have hchar : ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * (algebraMap F (AdeleRing (𝓞 F) F) ξ' + x)))
      = ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * x)) := by
    rw [mul_add, neg_add, ψ.map_add_eq_mul, h1, one_mul]
  rw [hgrp, hchar]

private theorem whittakerCoefficient_bruhatSeries_eq {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hN : ∀ (x : AdeleRing (𝓞 F) F) (g' : AdelicGL2 (𝓞 F) F), φ (unipotentGL2 x * g') = φ g')
    {ξ : F} (hξ : ξ ≠ 0) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    whittakerCoefficient F (productionPins F) ψ (bruhatSeries φ) ξ g
      = ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal •
          ∫ y, jacquetIntegrand ψ φ ξ g y ∂(adelicAddHaar (𝓞 F) F) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have hJ := integrable_jacquetIntegrand hψ ξ g hint
  rw [whittakerCoefficient_productionPins_eq]
  congr 1
  simp_rw [integrand_eq hψ hN ξ g]
  have h1 : IntegrableOn (fun x => φ g * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * x))) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) := by
    refine Measure.integrableOn_of_bounded (M := ‖φ g‖) (measure_adelicBox_lt_top F _).ne ?_ ?_
    · exact (continuous_const.mul (hψ.continuous.comp ((continuous_const.mul continuous_id).neg))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        rw [norm_mul, NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ, mul_one]
  have h2 := integrableOn_adelicBox_tsum_translate F (jacquetIntegrand ψ φ ξ g) hJ
  rw [integral_add h1 h2, integral_const_mul, setIntegral_adelicBox_addChar_neg_algebraMap_mul F ψ hψ hξ, mul_zero,
    zero_add, setIntegral_adelicBox_tsum_translate_eq F (jacquetIntegrand ψ φ ξ g) hJ]

private theorem whittakerCoefficient_bruhatSeries_eq_of_isInducedSection {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    (hψ : IsGlobalAddChar F ψ) {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) {ξ : F} (hξ : ξ ≠ 0) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    whittakerCoefficient F (productionPins F) ψ (bruhatSeries φ) ξ g
      = ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal • ∫ y, jacquetIntegrand ψ φ ξ g y ∂(adelicAddHaar (𝓞 F) F) :=
  whittakerCoefficient_bruhatSeries_eq hψ (fun x g' => isInducedSection_unipotent_mul hφ x g') hξ g hint

end WhittakerUnfolding
p2m_reactivate "P2MW.S_EisensteinGeneral_Unfolding_whittakerCoefficient_bruhatSeries_eq_of_isInducedSection.WhittakerUnfolding"

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel in
theorem solution
    {F : Type} [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    (hψ : IsGlobalAddChar F ψ) {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) {ξ : F} (hξ : ξ ≠ 0) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    whittakerCoefficient F (productionPins F) ψ
        (fun g' : AdelicGL2 (𝓞 F) F =>
          φ g' + ∑' ξ' : F,
            φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) ξ g
      = ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal •
          ∫ y, φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g) *
            ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y))
           ∂(adelicAddHaar (𝓞 F) F) :=
  WhittakerUnfolding.whittakerCoefficient_bruhatSeries_eq_of_isInducedSection hψ hφ hξ g hint

#print axioms solution

end
end S_EisensteinGeneral_Unfolding_whittakerCoefficient_bruhatSeries_eq_of_isInducedSection
end P2MW
export P2MW.S_EisensteinGeneral_Unfolding_whittakerCoefficient_bruhatSeries_eq_of_isInducedSection (solution)
