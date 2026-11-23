-- Prove2me | solution 1 for CompanionTheory.D.LK.lift_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:04.096157+00:00
-- url     : https://prove2.me/submissions/69bcbda7-cfee-4b55-95ef-0543220389fd

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Theorems.Thm_CompanionTheory_D_LK_bd_apply
import Theorems.Thm_CompanionTheory_D_LK_lift_ann
import Theorems.Thm_CompanionTheory_D_LK_lift_cre
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
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.D.LK
theorem _root_.solution {ε : Fin n → Bool} (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ i : Pos n, cpt ε i → ∀ x, φ (E i.1.1 i.1.2 x) = F i.1.1 i.1.2 (φ x))
    (x : Cn n V) : lift n φ (bd ε E x) = bd ε F (lift n φ x) := by
  funext A
  rw [lift_apply, bd_apply, bd_apply, map_add, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [h i hi, ← lift_ann]; rfl
    · exact map_zero _
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · rw [← lift_ann, ← lift_ann, ← lift_cre]; rfl
    · exact map_zero _
end CompanionTheory.D.LK
