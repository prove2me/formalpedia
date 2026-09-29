-- Prove2me | solution 1 for AutomorphicForm.whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f16ed70b-5f4d-5a30-a4ec-666de60cd65f

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient
import Theorems.Thm_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero.AutomorphicForm"
open MeasureTheory Matrix

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsIsotypicCuspFormAt productionPinsOf AdelicGL2 globalPoints finiteAdelicGL2Subgroup lsXiMemberAt_iff unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add IsCuspidalFn HeckeEigensystem IsPrincipalInvariantAddChar IsGlobalAddChar whittakerCoefficient whittakerCoefficient_zero_eq_constantTerm hasSum_whittakerCoefficient"
namespace WhittakerOneNeZeroSol
p2m_open "AutomorphicForm"

section Unipotent

variable {A : Type*} [CommRing A]

theorem unipotentGL2_inv (t : A) : (unipotentGL2 t)⁻¹ = unipotentGL2 (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

variable [TopologicalSpace A]

theorem continuous_unipotentGL2_val :
    Continuous fun t : A => ((unipotentGL2 t : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [unipotentGL2_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    fun_prop

variable [IsTopologicalRing A]

theorem continuous_unipotentGL2 : Continuous fun t : A => (unipotentGL2 t : GL (Fin 2) A) := by
  refine Units.continuous_iff.2 ⟨continuous_unipotentGL2_val, ?_⟩
  have h : (fun t : A => (((unipotentGL2 t)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A))
      = (fun t : A => ((unipotentGL2 t : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)) ∘ Neg.neg := by
    funext t
    simp only [Function.comp_apply, unipotentGL2_inv]
  rw [h]
  exact continuous_unipotentGL2_val.comp continuous_neg

end Unipotent

section Diagonal

variable (F : Type) [Field F]

def diagAlphaOne (α : F) (hα : α ≠ 0) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![α, 0; 0, 1] (by
    rw [Matrix.det_fin_two_of]; simpa using hα)

@[scoped simp] theorem diagAlphaOne_coe (α : F) (hα : α ≠ 0) :
    ((diagAlphaOne F α hα : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![α, 0; 0, 1] := rfl

variable [NumberField F]

theorem unipotentGL2_mul_globalPoints_diag (α : F) (hα : α ≠ 0) (x : AdeleRing (𝓞 F) F) :
    unipotentGL2 x * globalPoints (𝓞 F) F (diagAlphaOne F α hα)
      = globalPoints (𝓞 F) F (diagAlphaOne F α hα)
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) α⁻¹ * x) := by
  apply Units.ext
  have hαA : algebraMap F (AdeleRing (𝓞 F) F) α * algebraMap F (AdeleRing (𝓞 F) F) α⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hα, map_one]
  simp only [Units.val_mul, unipotentGL2_coe, globalPoints]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ← mul_assoc, hαA]

theorem unipotentGL2_algebraMap (k : F) :
    (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) k) : AdelicGL2 (𝓞 F) F)
      = globalPoints (𝓞 F) F (unipotentGL2 k) := by
  apply Units.ext
  simp only [unipotentGL2_coe, globalPoints]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map_apply]

end Diagonal

section Transport

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel

theorem whittakerCoefficient_eq_one_diag
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (α : F) (hα : α ≠ 0) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g
      = whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
          (globalPoints (𝓞 F) F (diagAlphaOne F α hα) * g) := by

  set f : AdeleRing (𝓞 F) F → ℂ := fun x =>
    φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) α⁻¹ * x) * g) * ψ (-x) with hf_def
  have hf : ∀ (k : F) (x : AdeleRing (𝓞 F) F),
      f (algebraMap F (AdeleRing (𝓞 F) F) k + x) = f x := by
    intro k x
    simp only [hf_def]
    rw [mul_add, ← map_mul, unipotentGL2_add, unipotentGL2_algebraMap, mul_assoc, hleft,
      neg_add, AddChar.map_add_eq_mul, ← map_neg, hψ (-k), one_mul]
  have hcov := NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap F hf α hα

  have hL : whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g
      = ∫ x, f (algebraMap F (AdeleRing (𝓞 F) F) α * x)
          ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
    show (∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
        ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F))) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf_def]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hα, map_one, one_mul]

  have hR : whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
        (globalPoints (𝓞 F) F (diagAlphaOne F α hα) * g)
      = ∫ x, f x ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
    show (∫ x, φ (unipotentGL2 x * (globalPoints (𝓞 F) F (diagAlphaOne F α hα) * g))
        * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * x))
        ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F))) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf_def]
    rw [← mul_assoc, unipotentGL2_mul_globalPoints_diag, mul_assoc, hleft, map_one, one_mul]
  rw [hL, hR, hcov]

end Transport

section Assembly

variable (F : Type) [Field F] [NumberField F]

theorem eq_zero_of_whittakerCoefficient_one_eq_zero
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hcusp : ∀ g : AdelicGL2 (𝓞 F) F,
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 0 g = 0)
    (hW : whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1 = 0) :
    φ = 0 := by
  funext g₀
  have hcoef : ∀ α : F,
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g₀ = 0 := by
    intro α
    rcases eq_or_ne α 0 with rfl | hα
    · exact hcusp g₀
    · rw [whittakerCoefficient_eq_one_diag F D U gen ψ hψ.principalInvariant φ hleft α hα g₀, hW]
      rfl
  have hslice : Continuous (fun x => φ (unipotentGL2 x * g₀)) :=
    hcont.comp (continuous_unipotentGL2.mul continuous_const)
  have h0 : HasSum (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g₀) 0 := by
    have : (fun α : F =>
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g₀)
        = fun _ => 0 := funext hcoef
    rw [this]
    exact hasSum_zero
  have hs := AutomorphicForm.hasSum_whittakerCoefficient F D U gen ψ hψ φ g₀ hslice h0.summable
  exact hs.unique h0

end Assembly

end AutomorphicForm.WhittakerOneNeZeroSol
p2m_reactivate "P2MW.S_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero.AutomorphicForm P2MW.S_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero.AutomorphicForm.WhittakerOneNeZeroSol"
p2m_reactivate "P2MW.S_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero.AutomorphicForm P2MW.S_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero.AutomorphicForm.WhittakerOneNeZeroSol"

open AutomorphicForm.WhittakerOneNeZeroSol in
theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (ξ : (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
      (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
      (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ξ N S Φ φ)
    (hφ : φ ≠ 0) :
    whittakerCoefficient ℚ (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
      (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ φ 1 ≠ 0 := by
  intro hW
  apply hφ

  have hcuspAt := hiso.smoothCusp.1
  have hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g := by
    letI : MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 ℚ) ℚ
    exact ((lsXiMemberAt_iff (𝓞 ℚ) ℚ _ _ ξ _ φ).mp hcuspAt.1).1.left_invariant
  have hcuspfn := hcuspAt.2
  refine eq_zero_of_whittakerCoefficient_one_eq_zero ℚ D _ _ NumberField.StandardAddChar.psiQ
    NumberField.StandardAddChar.isGlobalAddChar_psiQ φ hiso.continuous hleft (fun g => ?_) hW
  rw [whittakerCoefficient_zero_eq_constantTerm]
  exact hcuspfn g

end S_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_whittakerCoefficient_one_ne_zero_of_isIsotypicCuspFormAt_of_ne_zero (solution)
