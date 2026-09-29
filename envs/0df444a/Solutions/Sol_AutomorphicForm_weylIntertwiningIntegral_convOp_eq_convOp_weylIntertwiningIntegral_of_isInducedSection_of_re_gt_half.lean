-- Prove2me | solution 1 for AutomorphicForm.weylIntertwiningIntegral_convOp_eq_convOp_weylIntertwiningIntegral_of_isInducedSection_of_re_gt_half
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/60b4ea88-7502-5c57-9977-9aad67e8ad60

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Theorems.Thm_AutomorphicForm_weylIntertwiningIntegrand_integrable_of_re_gt_half
import Theorems.Thm_AutomorphicForm_continuous_weylIntertwiningIntegral_of_re_gt_half
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_weylIntertwiningIntegral_convOp_eq_convOp_weylIntertwiningIntegral_of_isInducedSection_of_re_gt_half
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open scoped ENNReal
open AutomorphicForm

namespace Ws31
namespace RNCommute

theorem isInducedSection_norm (K : Type) [Field K] [NumberField K]
    (αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 K) K μ) (hν : IsUnitaryChar (𝓞 K) K ν)
    (s : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) φ) :
    IsInducedSection (𝓞 K) K (etaFst 1 αm hαm (s.re : ℂ)) (etaSnd 1 αm hαm (s.re : ℂ))
      (fun g => ((‖φ g‖ : ℝ) : ℂ)) := by
  intro b hb g
  have h := hφ b hb g
  dsimp only
  rw [h, norm_mul, norm_mul, Complex.ofReal_mul, Complex.ofReal_mul]
  congr 1
  congr 1
  ·
    rw [etaFst_apply, etaFst_apply, Units.val_mul, Units.val_mul, norm_mul, hμ, one_mul,
      norm_cpowChar_apply, cpowChar_apply_val, MonoidHom.one_apply, Units.val_one, one_mul,
      re_add_half]
    have e : ((s.re : ℂ) + 1 / 2) = ((s.re + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, ← Complex.ofReal_cpow (hαm _).le]
  ·
    rw [etaSnd_apply, etaSnd_apply, Units.val_mul, Units.val_mul, norm_mul, hν, one_mul,
      norm_cpowChar_apply, cpowChar_apply_val, MonoidHom.one_apply, Units.val_one, one_mul]
    have e1 : (-(s + 1 / 2)).re = -(s.re + 1 / 2) := by rw [Complex.neg_re, re_add_half]
    have e : (-((s.re : ℂ) + 1 / 2)) = ((-(s.re + 1 / 2) : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e, ← Complex.ofReal_cpow (hαm _).le]

end Ws31.RNCommute

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (s : ℂ) (_hs : (1 / 2 : ℝ) < s.re)
      (φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ)
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
    ∀ g : AdelicGL2 (𝓞 K) K,
      weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (convOp K f φ) g =
        convOp K f (weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) φ) g := by
  intro αm
  intro hαm μ ν hμ hν s hs φ hφ hφc f hf hfc g
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  haveI : (adelicAddHaar (𝓞 K) K).IsAddHaarMeasure := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  set μA : Measure (AdeleRing (𝓞 K) K) := adelicAddHaar (𝓞 K) K with hμA
  set μG : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμG
  haveI : SigmaFinite μA := by rw [hμA]; infer_instance
  haveI : SigmaFinite μG := by rw [hμG]; infer_instance

  set F : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K → ℂ :=
    fun p => φ ((adelicWeyl (𝓞 K) K)⁻¹ * unipotentGL2 p.1 * (g * p.2)) * f p.2 with hF
  have hpath : Continuous fun p : AdeleRing (𝓞 K) K × AdelicGL2 (𝓞 K) K =>
      (adelicWeyl (𝓞 K) K)⁻¹ * unipotentGL2 p.1 * (g * p.2) :=
    (continuous_const.mul (AutomorphicForm.continuous_unipotentGL2.comp continuous_fst)).mul
      (continuous_const.mul continuous_snd)
  have hFc : Continuous F := (hφc.comp hpath).mul (hf.comp continuous_snd)
  have hFm : AEStronglyMeasurable F (μA.prod μG) := hFc.aestronglyMeasurable

  have hfib : ∀ y : AdelicGL2 (𝓞 K) K, Integrable (fun x => F (x, y)) μA := by
    intro y
    have h := AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half K hαm μ ν hμ hν s hs φ hφ hφc (g * y)
    exact h.mul_const (f y)

  set ψ : AdelicGL2 (𝓞 K) K → ℂ := fun h => ((‖φ h‖ : ℝ) : ℂ) with hψ
  have hψsec : IsInducedSection (𝓞 K) K (etaFst 1 αm hαm (s.re : ℂ)) (etaSnd 1 αm hαm (s.re : ℂ)) ψ :=
    Ws31.RNCommute.isInducedSection_norm K αm hαm μ ν hμ hν s φ hφ
  have hψc : Continuous ψ := Complex.continuous_ofReal.comp (continuous_norm.comp hφc)
  have h1u : IsUnitaryChar (𝓞 K) K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := fun x => by simp
  have hs' : 1 / 2 < ((s.re : ℂ)).re := by rwa [Complex.ofReal_re]
  have hMψ : Continuous (weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) ψ) :=
    AutomorphicForm.continuous_weylIntertwiningIntegral_of_re_gt_half K hαm 1 1 h1u h1u (s.re : ℂ) hs' ψ hψsec hψc
  have hnorm : ∀ y : AdelicGL2 (𝓞 K) K, ∫ x, ‖F (x, y)‖ ∂μA =
      (weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) ψ (g * y)).re * ‖f y‖ := by
    intro y
    have e : (fun x => ‖F (x, y)‖) =
        fun x => ‖φ ((adelicWeyl (𝓞 K) K)⁻¹ * unipotentGL2 x * (g * y))‖ * ‖f y‖ := by
      funext x; simp only [hF, norm_mul]
    rw [e, integral_mul_const]
    congr 1
    show (∫ x, ‖φ ((adelicWeyl (𝓞 K) K)⁻¹ * unipotentGL2 x * (g * y))‖ ∂μA) =
      (∫ x, ((‖φ ((adelicWeyl (𝓞 K) K)⁻¹ * unipotentGL2 x * (g * y))‖ : ℝ) : ℂ) ∂μA).re
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have hmaj : Integrable (fun y => ∫ x, ‖F (x, y)‖ ∂μA) μG := by
    have e : (fun y => ∫ x, ‖F (x, y)‖ ∂μA) =
        fun y => (weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) ψ (g * y)).re * ‖f y‖ :=
      funext hnorm
    rw [e]
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (Complex.continuous_re.comp (hMψ.comp (continuous_const.mul continuous_id))).mul hf.norm
    · exact hfc.norm.mul_left
  have hInt : Integrable F (μA.prod μG) :=
    (integrable_prod_iff' hFm).2 ⟨Filter.Eventually.of_forall hfib, hmaj⟩

  have L : weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (convOp K f φ) g =
      ∫ x, ∫ y, F (x, y) ∂μG ∂μA := by
    show (∫ x, convOp K f φ ((adelicWeyl (𝓞 K) K)⁻¹ * unipotentGL2 x * g) ∂μA) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (∫ y, φ ((adelicWeyl (𝓞 K) K)⁻¹ * unipotentGL2 x * g * y) * f y ∂μG) = ∫ y, F (x, y) ∂μG
    simp only [hF, mul_assoc]
  have R : convOp K f (weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) φ) g =
      ∫ y, ∫ x, F (x, y) ∂μA ∂μG := by
    show (∫ y, weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) φ (g * y) * f y ∂μG) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (∫ x, φ ((adelicWeyl (𝓞 K) K)⁻¹ * unipotentGL2 x * (g * y)) ∂μA) * f y = ∫ x, F (x, y) ∂μA
    rw [← integral_mul_const]
  rw [L, R]
  exact integral_integral_swap (f := fun x y => F (x, y)) hInt

end S_AutomorphicForm_weylIntertwiningIntegral_convOp_eq_convOp_weylIntertwiningIntegral_of_isInducedSection_of_re_gt_half
end P2MW
export P2MW.S_AutomorphicForm_weylIntertwiningIntegral_convOp_eq_convOp_weylIntertwiningIntegral_of_isInducedSection_of_re_gt_half (solution)
