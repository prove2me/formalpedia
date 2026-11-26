-- Prove2me | solution 1 for BKARMirror.reachable_thresholdGraph_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:08.875459+00:00
-- url     : https://prove2.me/submissions/d81dabb6-cd65-40e2-93f1-08312a80ba8c

import Mathlib
import Definitions.Def_BKAR
import Definitions.Def_Audit_ForestFormula_SolutionBasic
import Theorems.Thm_BKARMirror_edgeSetGraph_reachable_iff_exists_isSimplePath
import Theorems.Thm_BKARMirror_thresholdConnected_iff_exists_isSimplePath
import Theorems.Thm_BKARMirror_thresholdGraph_eq

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
open BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKARMirror
theorem _root_.solution (J : ForestIndex V)
    (data : BKAR.AcyclicEdgeSetData J.edges)
    (u : {e : Edge V // e ∈ J.edges} → ℝ) (s : ℝ) (e : Edge V) :
    (thresholdGraph J u s).Reachable e.left e.right ↔
      (data.toForest).thresholdConnected u s e.left e.right := by
  rw [thresholdGraph_eq J data u s]
  rw [edgeSetGraph_reachable_iff_exists_isSimplePath]
  exact (thresholdConnected_iff_exists_isSimplePath data.toForest u s e.left e.right).symm
end BKARMirror
