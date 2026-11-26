-- Prove2me | solution 1 for BKAR.Forest.standardInterp_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:14.721081+00:00
-- url     : https://prove2.me/submissions/479ddcaa-165f-483e-b57d-8848b5505c14

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_pathMin_singleton
import Theorems.Thm_BKAR_Forest_pathInF_eq_singleton_of_edge_mem


set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ)
    {e : Edge V} (he : e ∈ F.edges) :
    F.standardInterp u e = u ⟨e, he⟩ := by
  rw [standardInterp, dif_pos (F.edge_inSameComponent he),
    F.pathInF_eq_singleton_of_edge_mem he, F.pathMin_singleton u he]
end BKAR.Forest
