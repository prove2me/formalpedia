-- Prove2me | solution 1 for AutomorphicForm.summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/cf700da7-7a16-5d61-b928-6d6660ee5a58

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual
import Theorems.Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
import Theorems.Thm_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk place RingOfIntegers mixedEmbedding RingOfIntegers.coe_injective mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace AdeleRing mixedEmbedding_injective mixedEmbedding.integerLattice RingOfIntegers.coe_ne_zero_iff AdeleRing.principalSubgroup mixedEmbedding.finrank AdelicHaar.adeleBorel AdelicHaar.borelSpace_adeleBorel AdelicBox.integralFiniteAdeles AdelicLevel.glArch AdelicLevel.glArch_apply AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar"
namespace AdelicLevelAux
p2m_open "NumberField"

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

variable {F : Type} [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (NumberField.RingOfIntegers F) F
local notation "𝔸f" => FiniteAdeleRing (NumberField.RingOfIntegers F) F
local notation "𝔸i" => InfiniteAdeleRing F

private lemma valued_algebraMap_eq {v : HeightOneSpectrum (NumberField.RingOfIntegers F)}
    (N : NumberField.RingOfIntegers F) :
    Valued.v (algebraMap F (v.adicCompletion F)
        (algebraMap (NumberField.RingOfIntegers F) F N)) = v.intValuation N := by
  have h : Valued.v (algebraMap F (v.adicCompletion F)
      (algebraMap (NumberField.RingOfIntegers F) F N))
      = v.valuation F (algebraMap (NumberField.RingOfIntegers F) F N) :=
    valuedAdicCompletion_eq_valuation' v _
  rw [h, valuation_of_algebraMap]

private lemma exp_neg_one_pow (k : ℕ) : (exp (-1 : ℤ)) ^ k = exp (-(k : ℤ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, ← exp_add]
    congr 1
    push_cast
    ring

private lemma exists_pow_subset_of_mem_nhds
    {v : HeightOneSpectrum (NumberField.RingOfIntegers F)}
    {t : Set (v.adicCompletionIntegers F)} (ht : t ∈ nhds 0) :
    ∃ k : ℕ, ∀ (y : v.adicCompletion F) (hy : y ∈ v.adicCompletionIntegers F),
      Valued.v y ≤ exp (-(k : ℤ)) → (⟨y, hy⟩ : v.adicCompletionIntegers F) ∈ t := by
  obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).mp ht
  have h0 : ((0 : v.adicCompletionIntegers F) : v.adicCompletion F) = 0 := rfl
  rw [h0] at hu
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hu
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    (γ.isUnit.map MonoidWithZeroHom.ValueGroup₀.embedding).ne_zero
  obtain ⟨k, hk⟩ := exists_exp_neg_natCast_lt hγ0
  refine ⟨k, fun y hy hle => hut (hγ ?_)⟩
  simp only [Set.mem_setOf_eq]
  show Valued.v.restrict y < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  exact lt_of_le_of_lt hle hk

private theorem exists_level_smul_integral_subset {U : Set 𝔸f} (hU : U ∈ nhds (0 : 𝔸f)) :
    ∃ N : NumberField.RingOfIntegers F, N ≠ 0 ∧ ∀ r : 𝔸f,
      (∀ v, r v ∈ v.adicCompletionIntegers F) →
      algebraMap F 𝔸f (algebraMap (NumberField.RingOfIntegers F) F N) * r ∈ U := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := fun v =>
    Valued.isOpen_valuationSubring _
  set sm := RestrictedProduct.structureMap
      (fun w : HeightOneSpectrum (NumberField.RingOfIntegers F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (NumberField.RingOfIntegers F) =>
        (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      Filter.cofinite with hsmdef
  have hsm0 : sm 0 = (0 : 𝔸f) := by
    ext w
    rfl
  have hV : sm ⁻¹' U ∈ nhds 0 := by
    have hc : Continuous sm :=
      (RestrictedProduct.isOpenEmbedding_structureMap hAopen).continuous
    have := hc.continuousAt (x := 0)
    exact this.preimage_mem_nhds (by rwa [hsm0])
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, hIfin, t, ht, hsub⟩ := hV

  choose k hk using fun v : HeightOneSpectrum (NumberField.RingOfIntegers F) =>
    exists_pow_subset_of_mem_nhds (ht v)
  choose π hπmem hπne using fun v : HeightOneSpectrum (NumberField.RingOfIntegers F) =>
    Submodule.ne_bot_iff _ |>.mp v.ne_bot
  set N := ∏ v ∈ hIfin.toFinset, π v ^ k v with hNdef
  have hN0 : N ≠ 0 := by
    rw [hNdef]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hπne v)
  refine ⟨N, hN0, fun r hr => ?_⟩

  have hNval : ∀ v ∈ hIfin.toFinset, v.intValuation N ≤ exp (-(k v : ℤ)) := by
    intro v hv
    rw [hNdef, map_prod]
    rw [← Finset.prod_erase_mul _ _ hv]
    have h1 : v.intValuation (π v ^ k v) ≤ exp (-(k v : ℤ)) := by
      rw [map_pow, ← exp_neg_one_pow]
      refine pow_le_pow_left' ?_ _
      have := (v.intValuation_le_pow_iff_mem (π v) 1).mpr (by simpa using hπmem v)
      simpa using this
    have h2 : (∏ w ∈ hIfin.toFinset.erase v, v.intValuation (π w ^ k w)) ≤ 1 :=
      Finset.prod_le_one (fun _ _ => zero_le') (fun w _ => v.intValuation_le_one _)
    calc (∏ w ∈ hIfin.toFinset.erase v, v.intValuation (π w ^ k w))
          * v.intValuation (π v ^ k v)
        ≤ 1 * exp (-(k v : ℤ)) := mul_le_mul' h2 h1
      _ = exp (-(k v : ℤ)) := one_mul _

  set Nbar : F := algebraMap (NumberField.RingOfIntegers F) F N with hNbar
  have hmem : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers F),
      algebraMap F (v.adicCompletion F) Nbar * r v ∈ v.adicCompletionIntegers F := by
    intro v
    refine mul_mem ?_ (hr v)
    rw [mem_adicCompletionIntegers, hNbar, valued_algebraMap_eq]
    exact v.intValuation_le_one N
  set g : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨algebraMap F (v.adicCompletion F) Nbar * r v, hmem v⟩ with hgdef
  have hgpi : g ∈ Set.pi I t := by
    intro v hv
    have hvF : v ∈ hIfin.toFinset := hIfin.mem_toFinset.mpr hv
    refine hk v _ (hmem v) ?_
    rw [map_mul, valued_algebraMap_eq]
    calc v.intValuation N * Valued.v (r v)
        ≤ exp (-(k v : ℤ)) * 1 :=
          mul_le_mul' (hNval v hvF) ((mem_adicCompletionIntegers _ _ _).mp (hr v))
      _ = exp (-(k v : ℤ)) := mul_one _
  have hsmg : sm g = algebraMap F 𝔸f Nbar * r := by
    ext w
    have h1 : (sm g) w = algebraMap F (w.adicCompletion F) Nbar * r w := by
      simp [hsmdef, hgdef]
    have h2 : (algebraMap F 𝔸f Nbar * r) w
        = algebraMap F (w.adicCompletion F) Nbar * r w := rfl
    exact h1.trans h2.symm
  have := hsub hgpi
  rwa [Set.mem_preimage, hsmg] at this

end NumberField.AdelicLevelAux

set_option autoImplicit false

noncomputable section

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.NumberField NumberField.AdelicBox NumberField.AdelicHaar IsDedekindDomain AutomorphicForm"
open ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace WhittakerSummability
namespace Unfold

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

private def _root_.WhittakerSummability.Unfold.jacquetIntegrand (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (ξ : F)
    (g : AdelicGL2 (𝓞 F) F) (y : AdeleRing (𝓞 F) F) : ℂ :=
  φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y))

p2m_export "WhittakerSummability.Unfold" "jacquetIntegrand"
private theorem integrable_jacquetIntegrand {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (ξ : F) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    Integrable (jacquetIntegrand ψ φ ξ g) (adelicAddHaar (𝓞 F) F) := by
  refine hint.mul_bdd (c := 1) ?_ ?_
  · exact (hψ.continuous.comp ((continuous_const.mul continuous_id).neg)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => le_of_eq
      (NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ _)

private theorem integrand_eq {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hN : ∀ (x : AdeleRing (𝓞 F) F) (g' : AdelicGL2 (𝓞 F) F), φ (unipotentGL2 x * g') = φ g')
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
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hN : ∀ (x : AdeleRing (𝓞 F) F) (g' : AdelicGL2 (𝓞 F) F), φ (unipotentGL2 x * g') = φ g')
    {ξ : F} (hξ : ξ ≠ 0) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    whittakerCoefficient F (productionPins F) ψ (bruhatSeries φ) ξ g
      = ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal • ∫ y, jacquetIntegrand ψ φ ξ g y ∂(adelicAddHaar (𝓞 F) F) := by
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

end WhittakerSummability.Unfold
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold"
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold"

set_option autoImplicit false

noncomputable section

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.NumberField NumberField.AdelicHaar AutomorphicForm IsDedekindDomain FLT.SmoothVectors"
open scoped nonZeroDivisors

namespace WhittakerSummability
namespace Support

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "𝔸i" => InfiniteAdeleRing F

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private def finAdele (t : 𝔸f) : 𝔸 := ((0 : 𝔸i), t)

private def infAdele (x : 𝔸i) : 𝔸 := (x, (0 : 𝔸f))

@[scoped simp] private theorem finAdele_fst (t : 𝔸f) : (finAdele F t).1 = 0 := rfl
@[scoped simp] private theorem finAdele_snd (t : 𝔸f) : (finAdele F t).2 = t := rfl
private theorem finAdele_zero : finAdele F 0 = 0 := rfl

private theorem continuous_finAdele : Continuous (finAdele F) :=
  (continuous_const.prodMk continuous_id : Continuous fun t : 𝔸f => ((0 : 𝔸i), t))

private theorem algebraMap_mul_finAdele (ξ : F) (t : 𝔸f) :
    algebraMap F 𝔸 ξ * finAdele F t = finAdele F (algebraMap F 𝔸f ξ * t) := by
  refine Prod.ext ?_ ?_
  · show (algebraMap F 𝔸 ξ).1 * 0 = 0
    exact mul_zero _
  · rfl

private theorem algebraMap_mul_infAdele (a : F) (x : 𝔸i) :
    algebraMap F 𝔸 a * infAdele F x = infAdele F (algebraMap F 𝔸i a * x) := by
  refine Prod.ext ?_ ?_
  · rfl
  · show (algebraMap F 𝔸 a).2 * 0 = 0
    exact mul_zero _

private theorem continuous_unipotentGL2 : Continuous (fun u : 𝔸 => (unipotentGL2 u : AdelicGL2 (𝓞 F) F)) := by
  have hval : Continuous (fun u : 𝔸 =>
      ((unipotentGL2 u : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸)) := by
    refine continuous_matrix fun i j => ?_
    simp only [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have hinv : ∀ u : 𝔸, ((unipotentGL2 u)⁻¹ : AdelicGL2 (𝓞 F) F) = unipotentGL2 (-u) := fun u =>
    inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  simp_rw [hinv]
  exact hval.comp continuous_neg

private theorem glArch_unipotentGL2 (u : 𝔸) :
    NumberField.AdelicLevel.glArch (𝓞 F) F (unipotentGL2 u) = unipotentGL2 u.1 := by
  ext i j
  rw [NumberField.AdelicLevel.glArch_apply]
  fin_cases i <;> fin_cases j <;> rfl

private theorem conj_unipotentGL2_mem (g : AdelicGL2 (𝓞 F) F) (t : 𝔸f) :
    g⁻¹ * unipotentGL2 (finAdele F t) * g ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_mul, map_inv, glArch_unipotentGL2,
    finAdele_fst, unipotentGL2_zero, mul_one, inv_mul_cancel]

private def conjUnip (g : AdelicGL2 (𝓞 F) F) (t : 𝔸f) : finiteAdelicGL2Subgroup F :=
  ⟨g⁻¹ * unipotentGL2 (finAdele F t) * g, conj_unipotentGL2_mem F g t⟩

private theorem continuous_conjUnip (g : AdelicGL2 (𝓞 F) F) : Continuous (conjUnip F g) := by
  have h2 : Continuous (fun t : 𝔸f => (unipotentGL2 (finAdele F t) : AdelicGL2 (𝓞 F) F)) :=
    (continuous_unipotentGL2 F).comp (continuous_finAdele F)
  have h3 : Continuous (fun t : 𝔸f => g⁻¹ * unipotentGL2 (finAdele F t) * g) :=
    (h2.const_mul g⁻¹).mul_const g
  exact h3.subtype_mk _

private theorem conjUnip_zero (g : AdelicGL2 (𝓞 F) F) : conjUnip F g 0 = 1 := by
  refine Subtype.ext ?_
  show g⁻¹ * unipotentGL2 (finAdele F 0) * g = 1
  rw [finAdele_zero, unipotentGL2_zero, mul_one, inv_mul_cancel]

private theorem apply_mul_eq_of_mem_stabilizer {φ : AdelicGL2 (𝓞 F) F → ℂ} {u : finiteAdelicGL2Subgroup F}
    (hu : u ∈ MulAction.stabilizer (finiteAdelicGL2Subgroup F)
        (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ))
    (X : AdelicGL2 (𝓞 F) F) : φ (X * u) = φ X := by
  have h := MulAction.mem_stabilizer_iff.mp hu
  have hX := congrArg (fun f => RightTranslationFn.toFun f X) h
  simpa [Subgroup.smul_def] using hX

private theorem integral_eq_zero_of_period {ψ : AddChar 𝔸 ℂ} (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) (ξ : F) (t : 𝔸)
    (hfix : ∀ y : 𝔸, Φ (unipotentGL2 (t + y) * g) = Φ (unipotentGL2 y * g))
    (hψt : ψ (algebraMap F 𝔸 ξ * t) ≠ 1) :
    ∫ y, Φ (unipotentGL2 y * g) * ψ (-(algebraMap F 𝔸 ξ * y)) ∂(adelicAddHaar (𝓞 F) F) = 0 := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have hshift : ∀ y : 𝔸, Φ (unipotentGL2 (t + y) * g) * ψ (-(algebraMap F 𝔸 ξ * (t + y)))
      = ψ (-(algebraMap F 𝔸 ξ * t)) * (Φ (unipotentGL2 y * g) * ψ (-(algebraMap F 𝔸 ξ * y))) := by
    intro y
    rw [hfix y, mul_add, neg_add, AddChar.map_add_eq_mul]
    ring
  have key : ∫ y, Φ (unipotentGL2 y * g) * ψ (-(algebraMap F 𝔸 ξ * y)) ∂(adelicAddHaar (𝓞 F) F)
      = ∫ y, Φ (unipotentGL2 (t + y) * g) * ψ (-(algebraMap F 𝔸 ξ * (t + y))) ∂(adelicAddHaar (𝓞 F) F) :=
    (integral_add_left_eq_self (μ := adelicAddHaar (𝓞 F) F)
      (fun y => Φ (unipotentGL2 y * g) * ψ (-(algebraMap F 𝔸 ξ * y))) t).symm
  simp_rw [hshift] at key
  rw [integral_const_mul] at key
  have hc1 : ψ (-(algebraMap F 𝔸 ξ * t)) ≠ 1 := by
    intro h1
    apply hψt
    have hmul : ψ (-(algebraMap F 𝔸 ξ * t)) * ψ (algebraMap F 𝔸 ξ * t) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    rwa [h1, one_mul] at hmul
  have h0 : (1 - ψ (-(algebraMap F 𝔸 ξ * t)))
      * ∫ y, Φ (unipotentGL2 y * g) * ψ (-(algebraMap F 𝔸 ξ * y)) ∂(adelicAddHaar (𝓞 F) F) = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact key
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hc1))

private theorem lattice_of_level {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) {N : 𝓞 F} (hN : N ≠ 0) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ ξ : F,
      (∀ z ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 F) F,
          ψ (finAdele F (algebraMap F 𝔸f (ξ * algebraMap (𝓞 F) F N) * z)) = 1) →
      ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F D * ξ := by
  classical
  obtain ⟨a, ha0, ha⟩ :=
    NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hψ
  have hψa : IsGlobalAddChar F (ψ.mulShift (algebraMap F 𝔸 a)) :=
    { principalInvariant := fun q => by
        rw [AddChar.mulShift_apply, ← map_mul]
        exact hψ.principalInvariant (a * q)
      continuous := by
        change Continuous fun x : 𝔸 => ψ (algebraMap F 𝔸 a * x)
        exact hψ.continuous.comp (continuous_const_mul (algebraMap F 𝔸 a))
      nontrivial := by
        intro h
        apply hψ.nontrivial
        refine DFunLike.ext _ _ fun x => ?_
        have hx := DFunLike.congr_fun h (algebraMap F 𝔸 a⁻¹ * x)
        rw [AddChar.one_apply, AddChar.mulShift_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha0,
          map_one, one_mul] at hx
        rw [AddChar.one_apply]
        exact hx }
  have hinf : ∀ x : 𝔸i, ψ.mulShift (algebraMap F 𝔸 a) (x, 0)
      = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by
    intro x
    change ψ (algebraMap F 𝔸 a * infAdele F x) = _
    rw [algebraMap_mul_infAdele]
    exact ha x

  obtain ⟨m, hmS, hm⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).isFractional
  obtain ⟨q, hq⟩ := IsLocalization.exists_integer_multiple (𝓞 F)⁰ a
  obtain ⟨p, hp⟩ := hq
  refine ⟨m * N * q, mul_ne_zero (mul_ne_zero (nonZeroDivisors.ne_zero hmS) hN)
    (nonZeroDivisors.coe_ne_zero q), fun ξ hξ => ?_⟩
  have hmem : a⁻¹ * (ξ * algebraMap (𝓞 F) F N)
      ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) := by
    refine (NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual F hψa
      hinf _).mp fun z hz => ?_
    change ψ (algebraMap F 𝔸 a
      * finAdele F (algebraMap F 𝔸f (a⁻¹ * (ξ * algebraMap (𝓞 F) F N)) * z)) = 1
    rw [algebraMap_mul_finAdele, ← mul_assoc, ← map_mul, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
    exact hξ z hz

  obtain ⟨r, hr⟩ := hm _ hmem
  refine ⟨r * p, ?_⟩
  simp only [map_mul, hr, hp, Algebra.smul_def]
  have h1 : algebraMap (𝓞 F) F m * (a⁻¹ * (ξ * algebraMap (𝓞 F) F N)) * (algebraMap (𝓞 F) F q * a)
      = algebraMap (𝓞 F) F m * algebraMap (𝓞 F) F N * algebraMap (𝓞 F) F q * ξ * (a⁻¹ * a) := by
    ring
  rw [h1, inv_mul_cancel₀ ha0, mul_one]

private theorem integral_weyl_unipotent_eq_zero_of_forall_ne
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφf : IsKfSmooth F φ)
    (g : AdelicGL2 (𝓞 F) F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ ξ : F, (∀ a : 𝓞 F, (a : F) ≠ (d : F) * ξ) →
      ∫ y, φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)
          * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y)) ∂(adelicAddHaar (𝓞 F) F) = 0 := by
  classical

  have hSo : IsOpen ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
        Subgroup (finiteAdelicGL2Subgroup F)) : Set (finiteAdelicGL2Subgroup F)) := hφf
  have hLo := hSo.preimage (continuous_conjUnip F g)
  have h0L : (0 : 𝔸f) ∈ conjUnip F g ⁻¹' ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
        Subgroup (finiteAdelicGL2Subgroup F)) : Set (finiteAdelicGL2Subgroup F)) := by
    rw [Set.mem_preimage, conjUnip_zero]
    exact Subgroup.one_mem _
  obtain ⟨N, hN0, hN⟩ :=
    NumberField.AdelicLevelAux.exists_level_smul_integral_subset (hLo.mem_nhds h0L)

  obtain ⟨D, hD0, hD⟩ := lattice_of_level F hψ hN0
  refine ⟨D, hD0, fun ξ hξ => ?_⟩
  by_cases hall : ∀ z ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 F) F,
      ψ (finAdele F (algebraMap F 𝔸f (ξ * algebraMap (𝓞 F) F N) * z)) = 1
  · obtain ⟨a, ha⟩ := hD ξ hall
    exact absurd ha (hξ a)
  push Not at hall
  obtain ⟨z, hz, hz1⟩ := hall

  have htL := hN z hz
  rw [Set.mem_preimage] at htL
  have key := integral_eq_zero_of_period F (ψ := ψ) (fun x => φ (adelicWeyl (𝓞 F) F * x)) g ξ
    (finAdele F (algebraMap F 𝔸f (algebraMap (𝓞 F) F N) * z)) (fun y => ?_) ?_
  · simpa only [mul_assoc] using key
  · show φ (adelicWeyl (𝓞 F) F
        * (unipotentGL2 (finAdele F (algebraMap F 𝔸f (algebraMap (𝓞 F) F N) * z) + y) * g))
      = φ (adelicWeyl (𝓞 F) F * (unipotentGL2 y * g))
    have hgrp : adelicWeyl (𝓞 F) F
          * (unipotentGL2 (finAdele F (algebraMap F 𝔸f (algebraMap (𝓞 F) F N) * z) + y) * g)
        = adelicWeyl (𝓞 F) F * (unipotentGL2 y * g)
          * (conjUnip F g (algebraMap F 𝔸f (algebraMap (𝓞 F) F N) * z) : AdelicGL2 (𝓞 F) F) := by
      rw [add_comm, unipotentGL2_add]
      show _ = _ * (g⁻¹ * unipotentGL2 (finAdele F (algebraMap F 𝔸f (algebraMap (𝓞 F) F N) * z)) * g)
      group
    rw [hgrp]
    exact apply_mul_eq_of_mem_stabilizer F htL _
  · rw [algebraMap_mul_finAdele, ← mul_assoc, ← map_mul]
    exact hz1

end WhittakerSummability.Support
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"

noncomputable section

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.NumberField NumberField.AdelicHaar AutomorphicForm"

namespace WhittakerSummability
namespace Vanishing

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private theorem whittakerCoefficient_bruhatSeries_eq_zero_of_forall_ne (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (hφf : IsKfSmooth F φ) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ ξ : F, (∀ a : 𝓞 F, (a : F) ≠ (d : F) * ξ) →
      whittakerCoefficient F (productionPins F) ψ (WhittakerSummability.Unfold.bruhatSeries φ) ξ g = 0 := by
  obtain ⟨d, hd, hsup⟩ := WhittakerSummability.Support.integral_weyl_unipotent_eq_zero_of_forall_ne F hψ hφf g
  refine ⟨d, hd, fun ξ hξ => ?_⟩
  by_cases hξ0 : ξ = 0
  · exfalso
    refine hξ 0 ?_
    rw [hξ0, mul_zero]
    exact map_zero _
  · rw [WhittakerSummability.Unfold.whittakerCoefficient_bruhatSeries_eq_of_isInducedSection hψ hφ hξ0 g hint]
    have h0 : ∫ y, WhittakerSummability.Unfold.jacquetIntegrand ψ φ ξ g y ∂(adelicAddHaar (𝓞 F) F) = 0 := hsup ξ hξ
    rw [h0, smul_zero]

end WhittakerSummability.Vanishing
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"

set_option autoImplicit false

noncomputable section

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.NumberField NumberField.AdelicHaar AutomorphicForm"
open scoped NNReal

namespace WhittakerSummability
namespace Integrability

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private def haarModulus : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits

private theorem adelicWeyl_inv : (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv]

private theorem integrable_weyl_unipotent_mul (hα : ∀ x, 0 < ((haarModulus F x : ℝˣ) : ℝ))
    (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ₁ : IsUnitaryChar (𝓞 F) F χ₁) (hχ₂ : IsUnitaryChar (𝓞 F) F χ₂)
    (s : ℂ) (hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst χ₁ (haarModulus F) hα s) (etaSnd χ₂ (haarModulus F) hα s) φ)
    (hφc : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    Integrable (fun y : AdeleRing (𝓞 F) F => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g))
      (adelicAddHaar (𝓞 F) F) := by
  have h := AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα χ₁ χ₂
    hχ₁ hχ₂ s hs φ hφ hφc g
  simpa only [adelicWeyl_inv] using h

end WhittakerSummability.Integrability
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"

set_option autoImplicit false

noncomputable section

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.NumberField NumberField.AdelicHaar AutomorphicForm"
open scoped NNReal

namespace WhittakerSummability
namespace Decay

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

private def _root_.WhittakerSummability.Decay.jacquetIntegrand (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (ξ : F) (g : AdelicGL2 (𝓞 F) F) (y : AdeleRing (𝓞 F) F) : ℂ :=
  φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y))

p2m_export "WhittakerSummability.Decay" "jacquetIntegrand"
open scoped Classical in
private theorem norm_integral_jacquetIntegrand_le_polyDecay
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (s : ℂ) (_hs : 1 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφf : IsKfSmooth F φ)
      (_hφc : Continuous φ)
      (_hint : ∀ g' : AdelicGL2 (𝓞 F) F,
        Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g'))
          (adelicAddHaar (𝓞 F) F))
      (g : AdelicGL2 (𝓞 F) F) (N : ℕ),
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : F,
      ‖∫ y, jacquetIntegrand F ψ φ ξ g y ∂(adelicAddHaar (𝓞 F) F)‖ ≤
        C * (1 + ‖NumberField.mixedEmbedding F ξ‖) ^ (-(N : ℝ)) := by
  intro α hα χ₁ χ₂ hχ₁ hχ₂ ψ hψ s hs φ hφ hφK _hφf hφc _hint g N
  exact AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary F hα χ₁ χ₂ hχ₁ hχ₂
    ψ hψ s (lt_trans one_half_lt_one hs) φ hφ hφK hφc g N

end WhittakerSummability.Decay
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"

set_option autoImplicit false

noncomputable section

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.NumberField NumberField.AdelicBox NumberField.AdelicHaar AutomorphicForm"
open scoped NNReal ENNReal

namespace WhittakerSummability
namespace Assembly

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private theorem integrable_weyl_unipotent_mul_of_one_lt
    (hα : ∀ x, 0 < ((WhittakerSummability.Integrability.haarModulus F x : ℝˣ) : ℝ))
    (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ₁ : IsUnitaryChar (𝓞 F) F χ₁) (hχ₂ : IsUnitaryChar (𝓞 F) F χ₂)
    (s : ℂ) (hs : 1 < s.re)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst χ₁ (WhittakerSummability.Integrability.haarModulus F) hα s)
      (etaSnd χ₂ (WhittakerSummability.Integrability.haarModulus F) hα s) φ)
    (hφc : Continuous φ) (g' : AdelicGL2 (𝓞 F) F) :
    Integrable (fun y : AdeleRing (𝓞 F) F => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g'))
      (adelicAddHaar (𝓞 F) F) :=
  WhittakerSummability.Integrability.integrable_weyl_unipotent_mul F hα χ₁ χ₂ hχ₁ hχ₂ s (lt_trans (by norm_num) hs) φ hφ hφc g'

private theorem rpow_neg_le_mul_rpow_neg {X Y c : ℝ} (hX : 0 < X) (hY : 0 < Y) (hc : 0 < c)
    (hYX : Y ≤ c * X) (N : ℕ) :
    X ^ (-(N : ℝ)) ≤ c ^ N * Y ^ (-(N : ℝ)) := by
  rw [Real.rpow_neg hX.le, Real.rpow_neg hY.le, Real.rpow_natCast, Real.rpow_natCast]
  have h1 : Y ^ N ≤ c ^ N * X ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hY.le hYX N
  have h2 : (c ^ N * X ^ N)⁻¹ ≤ (Y ^ N)⁻¹ := inv_anti₀ (pow_pos hY N) h1
  calc (X ^ N)⁻¹ = c ^ N * (c ^ N * X ^ N)⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_pos hc N).ne', one_mul]
    _ ≤ c ^ N * (Y ^ N)⁻¹ := mul_le_mul_of_nonneg_left h2 (pow_pos hc N).le

open scoped Classical in

private theorem one_add_norm_mixedEmbedding_le (a : F) {d : F} (hd : d ≠ 0) :
    1 + ‖NumberField.mixedEmbedding F a‖ ≤
      max 1 ‖NumberField.mixedEmbedding F d‖ * (1 + ‖NumberField.mixedEmbedding F (a / d)‖) := by
  have hmul : NumberField.mixedEmbedding F a
      = NumberField.mixedEmbedding F (a / d) * NumberField.mixedEmbedding F d := by
    rw [← map_mul, div_mul_cancel₀ a hd]
  have h1 : ‖NumberField.mixedEmbedding F a‖
      ≤ ‖NumberField.mixedEmbedding F (a / d)‖ * max 1 ‖NumberField.mixedEmbedding F d‖ := by
    rw [hmul]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _))
  have hc1 : (1 : ℝ) ≤ max 1 ‖NumberField.mixedEmbedding F d‖ := le_max_left _ _
  have h0 : 0 ≤ ‖NumberField.mixedEmbedding F (a / d)‖ := norm_nonneg _
  linarith [h1, hc1, h0]

open scoped Classical in
private theorem norm_whittakerCoefficient_bruhatSeries_le
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F))
    {d : 𝓞 F} (hd : d ≠ 0) {C : ℝ} (hC : 0 < C) (N : ℕ)
    (hB : ∀ ξ : F, ‖∫ y, WhittakerSummability.Decay.jacquetIntegrand F ψ φ ξ g y ∂(adelicAddHaar (𝓞 F) F)‖ ≤
      C * (1 + ‖NumberField.mixedEmbedding F ξ‖) ^ (-(N : ℝ))) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ a : 𝓞 F,
      ‖whittakerCoefficient F (productionPins F) ψ (WhittakerSummability.Unfold.bruhatSeries φ) ((a : F) / d) g‖ ≤
        C' * (1 + ‖NumberField.mixedEmbedding F (a : F)‖) ^ (-(N : ℝ)) := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hm : 0 < ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr (adelicAddHaar_adelicBox_lt_top F).ne)
      (ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne')
  have hc : 0 < max 1 ‖NumberField.mixedEmbedding F (d : F)‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal * C * (max 1 ‖NumberField.mixedEmbedding F (d : F)‖) ^ N
      + ‖whittakerCoefficient F (productionPins F) ψ (WhittakerSummability.Unfold.bruhatSeries φ) 0 g‖,
    add_pos_of_pos_of_nonneg (mul_pos (mul_pos hm hC) (pow_pos hc N)) (norm_nonneg _), fun a => ?_⟩
  by_cases ha : a = 0
  ·
    subst ha
    have h0 : ((0 : 𝓞 F) : F) = 0 := map_zero (algebraMap (𝓞 F) F)
    rw [h0, zero_div, map_zero, norm_zero, add_zero, Real.one_rpow, mul_one]
    exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg hm.le hC.le) (pow_pos hc N).le)
  ·
    have ha' : (a : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ha
    have hξ : (a : F) / d ≠ 0 := div_ne_zero ha' hd'
    have hBξ : ‖∫ y, WhittakerSummability.Unfold.jacquetIntegrand ψ φ ((a : F) / d) g y ∂(adelicAddHaar (𝓞 F) F)‖ ≤
        C * (1 + ‖NumberField.mixedEmbedding F ((a : F) / d)‖) ^ (-(N : ℝ)) := hB ((a : F) / d)
    have hX : 0 < 1 + ‖NumberField.mixedEmbedding F ((a : F) / d)‖ := by positivity
    have hY : 0 < 1 + ‖NumberField.mixedEmbedding F (a : F)‖ := by positivity
    have hpow := rpow_neg_le_mul_rpow_neg hX hY hc (one_add_norm_mixedEmbedding_le F (a : F) hd') N
    rw [WhittakerSummability.Unfold.whittakerCoefficient_bruhatSeries_eq_of_isInducedSection hψ hφ hξ g hint, norm_smul,
      Real.norm_of_nonneg hm.le]
    calc ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal
          * ‖∫ y, WhittakerSummability.Unfold.jacquetIntegrand ψ φ ((a : F) / d) g y ∂(adelicAddHaar (𝓞 F) F)‖
        ≤ ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal
          * (C * ((max 1 ‖NumberField.mixedEmbedding F (d : F)‖) ^ N
            * (1 + ‖NumberField.mixedEmbedding F (a : F)‖) ^ (-(N : ℝ)))) :=
          mul_le_mul_of_nonneg_left (hBξ.trans (mul_le_mul_of_nonneg_left hpow hC.le)) hm.le
      _ = ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal * C * (max 1 ‖NumberField.mixedEmbedding F (d : F)‖) ^ N
          * (1 + ‖NumberField.mixedEmbedding F (a : F)‖) ^ (-(N : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg _))
          (Real.rpow_nonneg hY.le _)

open scoped Classical in
private theorem latticeBound_bruhatSeries
    (hα : ∀ x, 0 < ((WhittakerSummability.Integrability.haarModulus F x : ℝˣ) : ℝ))
    (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ₁ : IsUnitaryChar (𝓞 F) F χ₁) (hχ₂ : IsUnitaryChar (𝓞 F) F χ₂)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) (s : ℂ) (hs : 1 < s.re)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst χ₁ (WhittakerSummability.Integrability.haarModulus F) hα s)
      (etaSnd χ₂ (WhittakerSummability.Integrability.haarModulus F) hα s) φ)
    (hφK : IsArchKFinite F φ) (hφf : IsKfSmooth F φ) (hφc : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    ∃ (d : 𝓞 F) (C : ℝ) (N : ℕ), d ≠ 0 ∧ 0 < C ∧ Module.finrank ℚ F < N ∧
      (∀ ξ : F, (∀ a : 𝓞 F, (a : F) ≠ (d : F) * ξ) →
        whittakerCoefficient F (productionPins F) ψ (WhittakerSummability.Unfold.bruhatSeries φ) ξ g = 0) ∧
      (∀ a : 𝓞 F, ‖whittakerCoefficient F (productionPins F) ψ (WhittakerSummability.Unfold.bruhatSeries φ) ((a : F) / d) g‖
        ≤ C * (1 + ‖NumberField.mixedEmbedding F (a : F)‖) ^ (-(N : ℝ))) := by
  have hint : ∀ g' : AdelicGL2 (𝓞 F) F,
      Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g')) (adelicAddHaar (𝓞 F) F) :=
    fun g' => integrable_weyl_unipotent_mul_of_one_lt F hα χ₁ χ₂ hχ₁ hχ₂ s hs φ hφ hφc g'
  obtain ⟨d, hd, hS⟩ :=
    WhittakerSummability.Vanishing.whittakerCoefficient_bruhatSeries_eq_zero_of_forall_ne F hψ hφ hφf g (hint g)
  obtain ⟨C, hC, hB⟩ := WhittakerSummability.Decay.norm_integral_jacquetIntegrand_le_polyDecay F hα χ₁ χ₂ hχ₁ hχ₂ ψ hψ s hs
    φ hφ hφK hφf hφc hint g (Module.finrank ℚ F + 1)
  obtain ⟨C', hC', hB'⟩ := norm_whittakerCoefficient_bruhatSeries_le F hψ hφ g (hint g) hd hC
    (Module.finrank ℚ F + 1) hB
  exact ⟨d, C', Module.finrank ℚ F + 1, hd, hC', Nat.lt_succ_self _, hS, hB'⟩

end WhittakerSummability.Assembly
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.NumberField NumberField.AdelicHaar"
open AutomorphicForm
open scoped NNReal
open NumberField.mixedEmbedding Filter

noncomputable section

namespace WhittakerSummability
namespace LatticeSum

open scoped Classical in
private theorem latticeBound
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (s : ℂ) (_hs : 1 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφf : IsKfSmooth F φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    ∃ (d : 𝓞 F) (C : ℝ) (N : ℕ), d ≠ 0 ∧ 0 < C ∧ Module.finrank ℚ F < N ∧
      (∀ ξ : F, (∀ a : 𝓞 F, (a : F) ≠ (d : F) * ξ) → whittakerCoefficient F (productionPins F) ψ E ξ g = 0) ∧
      (∀ a : 𝓞 F, ‖whittakerCoefficient F (productionPins F) ψ E ((a : F) / d) g‖ ≤
        C * (1 + ‖NumberField.mixedEmbedding F (a : F)‖) ^ (-(N : ℝ))) := by
  intro α hα χ₁ χ₂ hχ₁ hχ₂ ψ hψ s hs φ hφ hφK hφf hφc g E
  exact WhittakerSummability.Assembly.latticeBound_bruhatSeries F hα χ₁ χ₂ hχ₁ hχ₂ ψ hψ s hs φ hφ hφK hφf hφc g

open scoped Classical in

private theorem summable_integers_rpow (F : Type*) [Field F] [NumberField F]
    (C : ℝ) (hC : 0 ≤ C) (N : ℕ) (hN : Module.finrank ℚ F < N) :
    Summable (fun a : 𝓞 F => C * (1 + ‖mixedEmbedding F (a : F)‖) ^ (-(N : ℝ))) := by
  classical
  set L : Submodule ℤ (mixedSpace F) := mixedEmbedding.integerLattice F with hL
  have hrank : Module.finrank ℤ L < N := by
    rw [hL, ZLattice.rank ℝ (mixedEmbedding.integerLattice F), mixedEmbedding.finrank]
    exact hN
  have hLsum : Summable (fun z : L => C * (1 + ‖z‖) ^ (-(N : ℝ))) := by
    refine Summable.of_norm_bounded_eventually
      ((ZLattice.summable_norm_pow_inv L N hrank).mul_left C) ?_
    filter_upwards [eventually_cofinite_ne (0 : L)] with z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hnn : 0 ≤ C * (1 + ‖z‖) ^ (-(N : ℝ)) := by positivity
    rw [Real.norm_of_nonneg hnn]
    have key : (1 + ‖z‖) ^ (-(N : ℝ)) ≤ ‖z‖⁻¹ ^ N := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖z‖), Real.rpow_natCast, inv_pow]
      exact inv_anti₀ (pow_pos hzpos N) (pow_le_pow_left₀ hzpos.le (by linarith) N)
    exact mul_le_mul_of_nonneg_left key hC

  let e : 𝓞 F → L := fun a => ⟨mixedEmbedding F (a : F), LinearMap.mem_range.mpr ⟨a, rfl⟩⟩
  have he : Function.Injective e := by
    intro a b h
    have h' : mixedEmbedding F (a : F) = mixedEmbedding F (b : F) := congrArg Subtype.val h
    exact RingOfIntegers.coe_injective (NumberField.mixedEmbedding_injective F h')
  have hrange : ∀ z ∉ Set.range e,
      (fun z : L => C * (1 + ‖z‖) ^ (-(N : ℝ))) z = 0 := by
    intro z hz
    exfalso
    apply hz
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp z.2
    exact ⟨a, Subtype.ext ha⟩
  exact (he.summable_iff hrange).mpr hLsum

open scoped Classical in
private theorem summable_of_lattice_bound {F : Type*} [Field F] [NumberField F] {W : F → ℂ}
    {d : 𝓞 F} (hd : d ≠ 0) {C : ℝ} (hC : 0 < C) {N : ℕ} (hN : Module.finrank ℚ F < N)
    (hsupp : ∀ ξ : F, (∀ a : 𝓞 F, (a : F) ≠ (d : F) * ξ) → W ξ = 0)
    (hbd : ∀ a : 𝓞 F, ‖W ((a : F) / d)‖ ≤ C * (1 + ‖mixedEmbedding F (a : F)‖) ^ (-(N : ℝ))) :
    Summable W := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  let ι : 𝓞 F → F := fun a => (a : F) / d
  have hι : Function.Injective ι := fun a b h =>
    RingOfIntegers.coe_injective ((div_left_inj' hd').mp h)
  have hoff : ∀ ξ ∉ Set.range ι, W ξ = 0 := by
    intro ξ hξ
    apply hsupp ξ
    intro a ha
    exact hξ ⟨a, by simp only [ι, ha, mul_div_cancel_left₀ _ hd']⟩
  refine (hι.summable_iff hoff).mp ?_
  exact Summable.of_norm_bounded (summable_integers_rpow F C hC.le N hN) (fun a => hbd a)

private theorem summable_of_latticeBound
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (s : ℂ) (_hs : 1 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφf : IsKfSmooth F φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    Summable (fun ξ : F => whittakerCoefficient F (productionPins F) ψ E ξ g) := by
  intro α hα χ₁ χ₂ hχ₁ hχ₂ ψ hψ s hs φ hφ hφK hφf hφc g E
  obtain ⟨d, C, N, hd, hC, hN, hsupp, hbd⟩ := latticeBound F hα χ₁ χ₂ hχ₁ hχ₂ ψ hψ s hs φ hφ hφK hφf hφc g
  exact summable_of_lattice_bound hd hC hN hsupp hbd

end WhittakerSummability.LatticeSum
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"

noncomputable section

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (s : ℂ) (_hs : 1 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφf : IsKfSmooth F φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    Summable (fun ξ : F => whittakerCoefficient F (productionPins F) ψ E ξ g) :=
  WhittakerSummability.LatticeSum.summable_of_latticeBound F

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Unfold P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.WhittakerSummability.Support"

end S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary
end P2MW
export P2MW.S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary (solution)
