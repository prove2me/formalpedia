-- Prove2me | solution 1 for DeletionCode.EditAlignment.Script.surviving_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:42.29812+00:00
-- url     : https://prove2.me/submissions/d5dd8aaa-58e5-4e43-895d-d8d8d90ecf58

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans
import Theorems.Thm_DeletionCode_EditAlignment_sublist_survives_delete

set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment
namespace DeletionCode.EditAlignment
namespace Script
theorem _root_.solution {y z : Word} {d i : ℕ} (h : Script y z d i) :
    ∃ w : Word, w.Sublist y ∧ w.Sublist z ∧ y.length ≤ w.length + d := by
  induction h with
  | refl => exact ⟨y, List.Sublist.refl _, List.Sublist.refl _, by omega⟩
  | @delete pre suffix bit d i h ih =>
    obtain ⟨w, hwy, hwz, hlen⟩ := ih
    obtain ⟨v, hvw, hvz, hvlen⟩ := sublist_survives_delete w pre suffix bit hwz
    exact ⟨v, hvw.trans hwy, hvz, by omega⟩
  | @insert pre suffix bit d i h ih =>
    obtain ⟨w, hwy, hwz, hlen⟩ := ih
    have hstep : (pre ++ suffix).Sublist (pre ++ bit :: suffix) :=
      (List.Sublist.refl pre).append ((List.Sublist.refl suffix).cons bit)
    exact ⟨w, hwy, hwz.trans hstep, hlen⟩
end Script
end DeletionCode.EditAlignment
