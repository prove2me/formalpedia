-- Prove2me | solution 1 for DeletionCode.EditAlignment.sublist_survives_delete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:44.142038+00:00
-- url     : https://prove2.me/submissions/2e460948-782f-46ce-9e65-83662fe4f4c6

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment

set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment
namespace DeletionCode.EditAlignment
theorem _root_.solution (w pre suffix : Word) (bit : Bool)
    (h : w.Sublist (pre ++ bit :: suffix)) :
    ∃ v : Word, v.Sublist w ∧ v.Sublist (pre ++ suffix) ∧ w.length ≤ v.length + 1 := by
  obtain ⟨left, right, rfl, hleft, hright⟩ := List.sublist_append_iff.mp h
  cases hright with
  | cons _ htail =>
    exact ⟨left ++ right, List.Sublist.refl _, hleft.append htail, by omega⟩
  | cons_cons _ htail =>
    rename_i tail
    refine ⟨left ++ tail, (List.Sublist.refl left).append ((List.Sublist.refl tail).cons bit),
      hleft.append htail, ?_⟩
    simp only [List.length_append, List.length_cons]
    omega
end DeletionCode.EditAlignment
