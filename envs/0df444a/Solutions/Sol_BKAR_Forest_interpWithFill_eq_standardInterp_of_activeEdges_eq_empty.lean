-- Prove2me | solution 1 for BKAR.Forest.interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:16.431369+00:00
-- url     : https://prove2.me/submissions/eb640ee3-591d-40c0-8d8a-c7c596c02e6e

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_mem_activeEdges_of_not_inSameComponent


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) (t : ℝ) (hF : F.activeEdges = ∅) :
    F.interpWithFill u t = F.standardInterp u := by
  funext e
  by_cases he : F.inSameComponent e.left e.right
  · rw [interpWithFill, standardInterp, dif_pos he, dif_pos he]
  · have hactive : e ∈ F.activeEdges :=
      F.mem_activeEdges_of_not_inSameComponent he
    have hempty : e ∈ (∅ : Finset (Edge V)) := by
      rw [← hF]
      exact hactive
    exact False.elim (Finset.notMem_empty e hempty)
end BKAR.Forest
