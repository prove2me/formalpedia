-- Prove2me | solution 1 for CompanionTheory.D.LK.kRel_tens
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:39.702143+00:00
-- url     : https://prove2.me/submissions/126510ef-aa4d-41c5-a0d1-b30c7e07d6c4

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_GeneralizedVermaModulePolynomial
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset MvPolynomial
open scoped TensorProduct
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Formalism.REAL GlobalTheory.CompanionTheory.DSVerma GlobalTheory.CompanionTheory.DSCover
open CompanionTheory.D.DSIC (KRel NC)
namespace CompanionTheory.D.LK
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {V Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]
    {E : Fin n → Fin n → Module.End ℂ V} {M : Fin n → Fin n → Module.End ℂ Z} (hE : KRel ε E) (hM : GlRel M) :
    KRel ε fun a b => ((E a b).rTensor Z + (M a b).lTensor V : Module.End ℂ (V ⊗[ℂ] Z)) := by
  intro a b c d h1 h2
  apply TensorProduct.ext'
  intro v z
  have e1 := LinearMap.congr_fun (hE a b c d h1 h2) v
  have e2 := LinearMap.congr_fun (hM a b c d) z
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at e1 e2
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, map_add, sub_eq_iff_eq_add.1 e1, sub_eq_iff_eq_add.1 e2, TensorProduct.add_tmul,
    TensorProduct.tmul_add, TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  split_ifs <;> simp <;> abel
end CompanionTheory.D.LK
