-- Prove2me | solution 1 for CompanionTheory.D.LK.evd_Ft_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:58.657841+00:00
-- url     : https://prove2.me/submissions/df654203-fc89-4501-921d-70e38a0bf2fb

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
import Theorems.Thm_CompanionTheory_D_LK_free_inter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.D.LK
theorem _root_.solution (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (b : FreeAlgebra ℂ (Fin n))
    (x : Cn n V) (A : Finset (Pos n)) :
    evd (Ft ε E) b x A = evd (fun c => E c c + (wt (A.filter (cpt ε)) c : ℂ) • 1) b (x A) :=
  free_inter (LinearMap.proj (R := ℂ) (φ := fun _ => V) A) _ _ (fun _ _ => rfl) b x
end CompanionTheory.D.LK
