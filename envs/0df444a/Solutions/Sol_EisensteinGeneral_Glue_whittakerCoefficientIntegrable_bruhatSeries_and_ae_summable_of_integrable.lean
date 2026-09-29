-- Prove2me | solution 1 for EisensteinGeneral.Glue.whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fa21e320-2441-5820-a656-8b58fad2699b

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Algebra.Module.ZLattice.Basic
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_EisensteinGeneral_Glue_whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable

set_option autoImplicit false

section Part1

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace EgenGlue

private scoped instance l1_nontrivial (F : Type) [Field F] [NumberField F] : Nontrivial (AdeleRing (𝓞 F) F) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  exact ⟨⟨0, 1, fun h => zero_ne_one (α := w.Completion) (congrArg (fun z : AdeleRing (𝓞 F) F => z.1 w) h)⟩⟩

private scoped instance l1_countable (F : Type) [Field F] [NumberField F] :
    Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  have hsurj : Function.Surjective
      (fun β : F => (⟨algebraMap F _ β, β, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F)) := by
    rintro ⟨_, β, rfl⟩; exact ⟨β, rfl⟩
  exact hsurj.countable

private noncomputable def l1_principalEquiv (F : Type) [Field F] [NumberField F] :
    F ≃ AdeleRing.principalSubgroup (𝓞 F) F :=
  Equiv.ofBijective (fun β => ⟨algebraMap F _ β, β, rfl⟩)
    ⟨fun a b h => (algebraMap F (AdeleRing (𝓞 F) F)).injective (congrArg Subtype.val h),
     by rintro ⟨_, β, rfl⟩; exact ⟨β, rfl⟩⟩

private theorem l1_integrable_tsum_and_ae_summable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ι : Type*} [Countable ι] {f : ι → X → ℂ} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hf' : ∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ ≠ ⊤) :
    Integrable (fun a => ∑' i, f i a) μ ∧ ∀ᵐ a ∂μ, Summable (fun i => f i a) := by
  have hf'' : ∀ i, AEMeasurable (fun a => ‖f i a‖ₑ) μ := fun i => (hf i).enorm
  have hhh : ∀ᵐ a ∂μ, Summable fun n => (‖f n a‖₊ : ℝ) := by
    rw [← lintegral_tsum hf''] at hf'
    refine (ae_lt_top' (AEMeasurable.tsum hf'') hf').mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  refine ⟨?_, hhh.mono fun a ha => ha.of_norm⟩
  refine ⟨?_, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
      (fun s => Finset.aestronglyMeasurable_fun_sum s fun i _ => hf i) ?_
    filter_upwards [hhh] with a ha
    exact (ha.of_norm).hasSum
  · have hlt : ∫⁻ a, ∑' n, ‖f n a‖ₑ ∂μ < ⊤ := by rwa [lintegral_tsum hf'', lt_top_iff_ne_top]
    exact lt_of_le_of_lt (lintegral_mono fun a => enorm_tsum_le_tsum_enorm) hlt

private theorem l1_tsum_lintegral_translate_eq (F : Type) [Field F] [NumberField F]
    (h : AdeleRing (𝓞 F) F → ℂ) :
    ∑' ξ : F, ∫⁻ x in adelicBox F, ‖h (algebraMap F (AdeleRing (𝓞 F) F) ξ + x)‖ₑ ∂(adelicAddHaar (𝓞 F) F)
      = ∫⁻ y, ‖h y‖ₑ ∂(adelicAddHaar (𝓞 F) F) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  rw [(isAddFundamentalDomain_adelicBox_adelicAddHaar F).lintegral_eq_tsum'' fun y => ‖h y‖ₑ]
  exact (l1_principalEquiv F).tsum_eq fun γ =>
    ∫⁻ x in adelicBox F, ‖h (γ +ᵥ x)‖ₑ ∂(adelicAddHaar (𝓞 F) F)

private theorem l1_integrableOn_translate (F : Type) [Field F] [NumberField F]
    (h : AdeleRing (𝓞 F) F → ℂ) (hh : Integrable h (adelicAddHaar (𝓞 F) F)) (ξ : F) :
    IntegrableOn (fun x => h (algebraMap F (AdeleRing (𝓞 F) F) ξ + x)) (adelicBox F) (adelicAddHaar (𝓞 F) F) := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  exact (hh.comp_add_left (algebraMap F (AdeleRing (𝓞 F) F) ξ)).integrableOn

private theorem l1_periodization (F : Type) [Field F] [NumberField F] (h : AdeleRing (𝓞 F) F → ℂ)
    (hh : Integrable h (adelicAddHaar (𝓞 F) F)) :
    Integrable (fun x => ∑' ξ : F, h (algebraMap F (AdeleRing (𝓞 F) F) ξ + x))
        ((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)) ∧
      ∀ᵐ x ∂((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)),
        Summable (fun ξ : F => h (algebraMap F (AdeleRing (𝓞 F) F) ξ + x)) := by
  refine l1_integrable_tsum_and_ae_summable
    (fun ξ => (l1_integrableOn_translate F h hh ξ).aestronglyMeasurable) ?_
  rw [l1_tsum_lintegral_translate_eq F h]
  exact hh.2.ne

end EgenGlue
p2m_reactivate "P2MW.S_EisensteinGeneral_Glue_whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable.EgenGlue"

end Part1
p2m_reactivate "P2MW.S_EisensteinGeneral_Glue_whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable.EgenGlue"

section Solution

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open EgenGlue in

theorem solution (F : Type) [Field F]
    [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ φ)
    (ξ : F) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    WhittakerCoefficientIntegrable F (productionPins F) ψ
        (fun g' => φ g' + ∑' ξ' : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g'))
        ξ g ∧
      (letI := (productionPins F).nS
        ∀ᵐ x ∂(productionPins F).ν, Summable (fun ξ' : F =>
          φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * (unipotentGL2 x * g)))) := by
  obtain ⟨_, _, hsec⟩ := hφ
  obtain ⟨hP, hPae⟩ := l1_periodization F _ hint
  have hsummand : ∀ (x : AdeleRing (𝓞 F) F) (ξ' : F),
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * (unipotentGL2 x * g))
        = φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ' + x) * g) := by
    intro x ξ'
    simp only [unipotentGL2_add, mul_assoc]
  refine ⟨?_, ?_⟩
  · show Integrable
        (fun x : AdeleRing (𝓞 F) F =>
          (φ (unipotentGL2 x * g) + ∑' ξ' : F,
              φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * (unipotentGL2 x * g)))
            * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * x)))
        (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
    unfold ProbabilityTheory.cond
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne')
    refine Integrable.mul_bdd (c := 1) ?_ ?_ ?_
    · have h1 : Integrable (fun x : AdeleRing (𝓞 F) F => φ (unipotentGL2 x * g))
          ((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)) := by
        haveI : IsFiniteMeasure ((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)) :=
          isFiniteMeasure_restrict.mpr (adelicAddHaar_adelicBox_lt_top F).ne
        have hconst : (fun x : AdeleRing (𝓞 F) F => φ (unipotentGL2 x * g)) = fun _ => φ g :=
          funext fun x => isInducedSection_unipotent_mul hsec x g
        rw [hconst]
        exact integrable_const _
      have h2 : Integrable (fun x : AdeleRing (𝓞 F) F => ∑' ξ' : F,
            φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * (unipotentGL2 x * g)))
          ((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)) := by
        refine Integrable.congr hP (Filter.Eventually.of_forall fun x => ?_)
        exact tsum_congr fun ξ' => (hsummand x ξ').symm
      exact h1.add h2
    · exact (hψc.comp ((continuous_const.mul continuous_id).neg)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => (hψ _).le
  · show ∀ᵐ x ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)), Summable (fun ξ' : F =>
        φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * (unipotentGL2 x * g)))
    unfold ProbabilityTheory.cond
    refine Measure.ae_smul_measure ?_ _
    refine hPae.mono fun x hx => ?_
    exact hx.congr fun ξ' => (hsummand x ξ').symm

end Solution
p2m_reactivate "P2MW.S_EisensteinGeneral_Glue_whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable.EgenGlue"

#print axioms solution

end S_EisensteinGeneral_Glue_whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable
end P2MW
export P2MW.S_EisensteinGeneral_Glue_whittakerCoefficientIntegrable_bruhatSeries_and_ae_summable_of_integrable (solution)
