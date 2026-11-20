-- Prove2me | solution 1 for DeletionCode.EditAlignment.alignment_of_common_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:42.742377+00:00
-- url     : https://prove2.me/submissions/db6f7e12-961c-40a0-ab6c-f408dacd3e92

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment
import Theorems.Thm_DeletionCode_EditAlignment_Alignment_from_empty

set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment
namespace DeletionCode.EditAlignment
theorem _root_.solution {w y z : Word}
    (hy : w.Sublist y) (hz : w.Sublist z) :
    Alignment y z (y.length - w.length) (z.length - w.length) := by
  induction hy generalizing z with
  | slnil => simpa using Alignment.from_empty z
  | cons bit h ih =>
    have hlength := h.length_le
    have halign := Alignment.deletion bit (ih hz)
    convert halign using 1
    simp only [List.length_cons]
    omega
  | @cons_cons w y bit h ih =>
    revert hz
    induction z with
    | nil => intro hz; cases hz
    | cons other z ihz =>
      intro hz
      cases hz with
      | cons _ hskip =>
        have hlength := hskip.length_le
        have halign := Alignment.insertion other (ihz hskip)
        convert halign using 1
        simp only [List.length_cons] at *
        omega
      | cons_cons _ hmatch =>
        simpa only [List.length_cons, Nat.add_sub_add_right] using
          Alignment.matched bit (ih hmatch)
end DeletionCode.EditAlignment
