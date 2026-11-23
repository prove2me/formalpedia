-- Prove2me | solution 1 for CompanionTheory.D.LK.filter_erase_of_not
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:39.738442+00:00
-- url     : https://prove2.me/submissions/aa5365ab-3a07-4e6f-9575-5e50c1b6157f

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
theorem _root_.solution {p : Pos n → Prop} [DecidablePred p] {k : Pos n} (hk : ¬p k) (A : Finset (Pos n)) :
    (A.erase k).filter p = A.filter p := by
  ext a
  simp only [mem_filter, mem_erase]
  exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨fun e => hk (e ▸ h.2), h.1⟩, h.2⟩⟩
end CompanionTheory.D.LK
