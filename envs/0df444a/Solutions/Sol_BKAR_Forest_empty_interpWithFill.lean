-- Prove2me | solution 1 for BKAR.Forest.empty_interpWithFill
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:15:29.536429+00:00
-- url     : https://prove2.me/submissions/42b09c2d-0274-45c4-8676-b316f8cce721

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
theorem _root_.solution (u : (Forest.empty V).EdgeParam → ℝ)
    (t : ℝ) :
    (Forest.empty V).interpWithFill u t = constantConfig t := by
  funext e
  rw [interpWithFill]
  rw [dif_neg]
  · rfl
  · intro hcomp
    exact e.left_ne_right ((Forest.empty_inSameComponent_iff.mp hcomp))
end BKAR.Forest
