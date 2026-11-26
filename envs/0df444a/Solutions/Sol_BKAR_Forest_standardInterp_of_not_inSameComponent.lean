-- Prove2me | solution 1 for BKAR.Forest.standardInterp_of_not_inSameComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:29.995948+00:00
-- url     : https://prove2.me/submissions/d97e2b9c-816a-4588-b873-6bf36d6022fb

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
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) :
    F.standardInterp u e = 0 := by
  rw [standardInterp, dif_neg he]
end BKAR.Forest
