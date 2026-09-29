-- Prove2me | solution 1 for AutomorphicForm.zetaIntegrand_whittakerCoefficient_unipotentAverage_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/78b002e5-c775-5207-a595-58b6593586d6

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicFourier
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentAverage_diagOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (G : AdelicGL2 (𝓞 F) F → ℂ) (hGc : Continuous G)
    (hMG : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖G g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M)
    (hGleft : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F), G (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = G g)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) :
    zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s a =
      (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * ψ (((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x) ∂(adelicAddHaar (𝓞 F) F)) *
      zetaIntegrand (fun g => whittakerCoefficient F (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 g) χ s a := by
  have h := AutomorphicForm.whittakerCoefficient_unipotentAverage_diagOne F D
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    ψ hψ G hGc hMG hGleft B hB Φ hΦ 1 a
  simp only [map_one, one_mul] at h
  simp only [zetaIntegrand, h]
  ring

end S_AutomorphicForm_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq_mul
end P2MW
export P2MW.S_AutomorphicForm_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq_mul (solution)
