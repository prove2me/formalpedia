-- Prove2me | solution 1 for BKAR.Forest.interpWithFill_of_not_inSameComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:19:42.808612+00:00
-- url     : https://prove2.me/submissions/acce42d6-811e-4092-94ce-aac5e6836e40

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) (t : ℝ) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) :
    F.interpWithFill u t e = t := by
  rw [interpWithFill, dif_neg he]
end BKAR.Forest
