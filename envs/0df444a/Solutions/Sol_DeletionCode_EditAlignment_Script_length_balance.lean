-- Prove2me | solution 1 for DeletionCode.EditAlignment.Script.length_balance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:43.658111+00:00
-- url     : https://prove2.me/submissions/b6532de3-47f3-425c-ad71-b816a9ccc300

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment

set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment
namespace DeletionCode.EditAlignment
namespace Script
theorem _root_.solution {y z : Word} {d i : ℕ} (h : Script y z d i) :
    z.length + d = y.length + i := by
  induction h with
  | refl => omega
  | delete h ih => simp only [List.length_append, List.length_cons] at *; omega
  | insert h ih => simp only [List.length_append, List.length_cons] at *; omega
end Script
end DeletionCode.EditAlignment
