-- Prove2me | solution 1 for DeletionCode.EditAlignment.Script.reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:43.201673+00:00
-- url     : https://prove2.me/submissions/680da5c4-7279-4acf-a0ed-53b572e4b865

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans

set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment
namespace DeletionCode.EditAlignment
namespace Script
theorem _root_.solution {y z : Word} {d i : ℕ} (h : Script y z d i) :
    Script z y i d := by
  induction h with
  | refl => exact Script.refl _
  | @delete pre suffix bit d i h ih =>
    have hfirst : Script (pre ++ suffix) (pre ++ bit :: suffix) 0 1 :=
      Script.insert (Script.refl _)
    simpa only [Nat.zero_add, Nat.add_comm 1 d] using hfirst.trans ih
  | @insert pre suffix bit d i h ih =>
    have hfirst : Script (pre ++ bit :: suffix) (pre ++ suffix) 1 0 :=
      Script.delete (Script.refl _)
    simpa only [Nat.zero_add, Nat.add_comm 1 i] using hfirst.trans ih
end Script
end DeletionCode.EditAlignment
