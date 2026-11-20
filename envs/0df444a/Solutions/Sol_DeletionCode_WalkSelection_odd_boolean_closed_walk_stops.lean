-- Prove2me | solution 1 for DeletionCode.WalkSelection.odd_boolean_closed_walk_stops
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:21:16.251946+00:00
-- url     : https://prove2.me/submissions/0bce8dcd-384e-4d1f-8bfb-b24e10319c27

import Definitions.Def_DeletionCode_ClosedWalk
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_DeletionCode_WalkSelection
import Theorems.Thm_DeletionCode_WalkSelection_odd_closed_walk_stops
import Theorems.Thm_DeletionCode_WalkSelection_ScanState_generating
import Theorems.Thm_DeletionCode_WalkSelection_ScanState_generating_after_append

set_option autoImplicit true
open DeletionCode DeletionCode.WalkSelection
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℚ V] {m : ℕ}
namespace DeletionCode.WalkSelection
theorem _root_.solution {H : Type*} (p : Fin (m + 1) → H → ℚ)
    (hp : ∀ j, WitnessAlgebra.BooleanVector (p j))
    (Good : Finset (Fin m) → Prop) (hgood : Good ∅)
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m) :
    ∃ (i : Fin m) (S : Finset (Fin m)),
      ScanState (walkStep p) Good i.val S ∧ GeneratingSelected p S ∧
      ¬ SignedMember (walkStep p) S (walkStep p i) ∧
        (walkStep p i ∈ selectedSpan (walkStep p) S ∨
          (walkStep p i ∉ selectedSpan (walkStep p) S ∧
            LinearIndepOn ℚ (walkStep p) ((insert i S : Finset (Fin m)) : Set (Fin m)) ∧
            ¬ Good (insert i S) ∧ GeneratingSelected p (insert i S))) := by
  obtain ⟨i, S, hs, hnew, hstop⟩ := odd_closed_walk_stops p Good hgood hclosed hodd
  refine ⟨i, S, hs, hs.generating hp, hnew, ?_⟩
  rcases hstop with hrel | ⟨hout, hind, hbad⟩
  · exact Or.inl hrel
  · exact Or.inr ⟨hout, hind, hbad, hs.generating_after_append hp i rfl hout⟩
end DeletionCode.WalkSelection
