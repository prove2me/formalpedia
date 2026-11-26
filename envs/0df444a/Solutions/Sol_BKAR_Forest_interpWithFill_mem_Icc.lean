-- Prove2me | solution 1 for BKAR.Forest.interpWithFill_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:11:50.633514+00:00
-- url     : https://prove2.me/submissions/e7c904e3-2a78-4eab-ad3d-60ae2ab5b49d

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_pathMin_mem_Icc

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) (e : Edge V) :
    0 ≤ F.interpWithFill u t e ∧ F.interpWithFill u t e ≤ 1 := by
  by_cases h : F.inSameComponent e.left e.right
  · rw [interpWithFill, dif_pos h]
    exact F.pathMin_mem_Icc u hu (F.pathInF e.left e.right h)
  · rw [interpWithFill, dif_neg h]
    exact ht
end BKAR.Forest
