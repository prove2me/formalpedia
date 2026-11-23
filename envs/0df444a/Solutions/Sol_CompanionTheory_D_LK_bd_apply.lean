-- Prove2me | solution 1 for CompanionTheory.D.LK.bd_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:13.620945+00:00
-- url     : https://prove2.me/submissions/84baba6a-70d0-4df4-9185-303605d99dab

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreApply
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
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
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (x : Cn n V) (A : Finset (Pos n)) :
    bd ε E x A = (∑ i : Pos n, if cpt ε i then E i.1.1 i.1.2 (ann i x A) else 0) +
      ∑ i : Pos n, ∑ j : Pos n, ∑ k : Pos n, if Tri ε i j k then cre k (ann j (ann i x)) A else 0 := by
  simp only [bd, LinearMap.add_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> rfl
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> rfl
end CompanionTheory.D.LK
