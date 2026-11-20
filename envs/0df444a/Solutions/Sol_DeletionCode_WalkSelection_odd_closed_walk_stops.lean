-- Prove2me | solution 1 for DeletionCode.WalkSelection.odd_closed_walk_stops
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:05.068012+00:00
-- url     : https://prove2.me/submissions/f32d1f62-731a-4f92-912b-100f35212ea2

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
import Theorems.Thm_DeletionCode_WalkSelection_scan_prefix
import Theorems.Thm_DeletionCode_ClosedWalk_not_odd_signed_independent_closed_walk


set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}
namespace DeletionCode.WalkSelection
theorem _root_.solution (p : Fin (m + 1) → V)
    (Good : Finset (Fin m) → Prop) (hgood : Good ∅)
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m) :
    Stopped (walkStep p) Good := by
  classical
  rcases scan_prefix (walkStep p) Good hgood m le_rfl with hstop | ⟨S, hs⟩
  · exact hstop
  · let label : Fin m → S := fun j =>
      ⟨Classical.choose (hs.covered j j.isLt),
        (Classical.choose_spec (hs.covered j j.isLt)).1⟩
    have hsteps : ∀ j : Fin m,
        p j.succ - p j.castSucc = walkStep p (label j).val ∨
        p j.succ - p j.castSucc = -walkStep p (label j).val :=
      fun j => (Classical.choose_spec (hs.covered j j.isLt)).2.2
    exact False.elim (ClosedWalk.not_odd_signed_independent_closed_walk
      (fun r : S => walkStep p r.val) hs.independent p label hclosed hsteps hodd)
end DeletionCode.WalkSelection
