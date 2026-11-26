-- Prove2me | solution 1 for BKAR.Forest.standardInterp_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:21.749561+00:00
-- url     : https://prove2.me/submissions/fd5fed17-fcc8-4465-a7ba-d91da2ff8d58

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
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1) (e : Edge V) :
    0 ≤ F.standardInterp u e ∧ F.standardInterp u e ≤ 1 := by
  by_cases h : F.inSameComponent e.left e.right
  · rw [standardInterp, dif_pos h]
    exact F.pathMin_mem_Icc u hu (F.pathInF e.left e.right h)
  · rw [standardInterp, dif_neg h]
    exact ⟨le_rfl, zero_le_one⟩
end BKAR.Forest
