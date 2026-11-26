-- Prove2me | solution 1 for BKAR.Forest.empty_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:26.68291+00:00
-- url     : https://prove2.me/submissions/945a638f-625d-4e75-a5f0-38823a58b343

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Edge_left_ne_right
import Theorems.Thm_BKAR_Forest_empty_inSameComponent_iff


set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (u : (Forest.empty V).EdgeParam → ℝ) :
    (Forest.empty V).standardInterp u = zeroConfig := by
  funext e
  rw [standardInterp]
  rw [dif_neg]
  · rfl
  · intro hcomp
    exact e.left_ne_right ((Forest.empty_inSameComponent_iff.mp hcomp))
end BKAR.Forest
