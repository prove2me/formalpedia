-- Prove2me | solution 1 for CompanionTheory.D.LK.evd_eig
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:58.552463+00:00
-- url     : https://prove2.me/submissions/7827f275-e067-4bda-b632-42a7526c1ad1

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
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
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight CasK Cas)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsDS rhoC)
open CompanionTheory.D.DSIC (KRel KUnit KStab LowSpan HWMap)
variable {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace CompanionTheory.D.LK
theorem _root_.solution (F : Fin n → Module.End ℂ V) (τ : Fin n → ℂ) (x : V) (h : ∀ c, F c x = τ c • x)
    (b : FreeAlgebra ℂ (Fin n)) : evd F b x = FreeAlgebra.lift ℂ τ b • x := by
  refine FreeAlgebra.induction ℂ (Fin n) (fun r => ?_) (fun c => ?_) (fun a b ha hb => ?_) (fun a b ha hb => ?_) b
  · simp only [AlgHom.commutes, Module.algebraMap_end_apply]
    rfl
  · simp only [CompanionTheory.D.LK.evd, FreeAlgebra.lift_ι_apply, h]
  · rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, map_mul, smul_smul, mul_comm]
  · rw [map_add, LinearMap.add_apply, ha, hb, map_add, add_smul]
end CompanionTheory.D.LK
