-- Prove2me | solution 1 for BKAR.Forest.standardInterp_eq_of_edges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:43:51.433799+00:00
-- url     : https://prove2.me/submissions/108c7311-6ad2-4802-ae52-c8cb0974f66e

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_pathMin_eq_of_forall
import Theorems.Thm_BKAR_Forest_inSameComponent_of_edges_eq
import Theorems.Thm_BKAR_Forest_pathInF_eq_of_edges_eq


set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F G : Forest V)
    (u : F.EdgeParam → ℝ) (v : G.EdgeParam → ℝ)
    (hedges : F.edges = G.edges)
    (hparam : ∀ e : Edge V, F.paramValue u e = G.paramValue v e) :
    F.standardInterp u = G.standardInterp v := by
  funext e
  by_cases hF : F.inSameComponent e.left e.right
  · have hG : G.inSameComponent e.left e.right :=
      F.inSameComponent_of_edges_eq G hedges hF
    rw [standardInterp, dif_pos hF]
    rw [standardInterp, dif_pos hG]
    rw [F.pathInF_eq_of_edges_eq G hedges hF hG]
    exact F.pathMin_eq_of_forall G u v
      (G.pathInF e.left e.right hG)
      (fun e' _he' => hparam e')
  · have hG : ¬ G.inSameComponent e.left e.right := by
      intro hG
      exact hF (G.inSameComponent_of_edges_eq F hedges.symm hG)
    rw [standardInterp, dif_neg hF]
    rw [standardInterp, dif_neg hG]
end BKAR.Forest
