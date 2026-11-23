-- Prove2me | solution 1 for CompanionTheory.D.LK.free_inter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:52.447243+00:00
-- url     : https://prove2.me/submissions/6537794c-2ba6-4d97-b43d-4eff360a473c

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
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
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.D.LK
theorem _root_.solution {ι : Type} (φ : V →ₗ[ℂ] W) (S : ι → Module.End ℂ V) (T : ι → Module.End ℂ W)
    (h : ∀ i x, φ (S i x) = T i (φ x)) (a : FreeAlgebra ℂ ι) :
    ∀ x, φ (FreeAlgebra.lift ℂ S a x) = FreeAlgebra.lift ℂ T a (φ x) := by
  induction a using FreeAlgebra.induction with
  | grade0 r => intro x; simp [Module.algebraMap_end_apply]
  | grade1 c => intro x; simp [h]
  | mul a b ha hb => intro x; simp only [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => intro x; simp only [map_add, LinearMap.add_apply, ha, hb]
end CompanionTheory.D.LK
