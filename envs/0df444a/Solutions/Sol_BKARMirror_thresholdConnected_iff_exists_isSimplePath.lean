-- Prove2me | solution 1 for BKARMirror.thresholdConnected_iff_exists_isSimplePath
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:14:46.480496+00:00
-- url     : https://prove2.me/submissions/76521bce-8c36-4301-8fc9-9a1bfda545dd

import Mathlib
import Definitions.Def_BKAR
import Definitions.Def_Audit_ForestFormula_SolutionBasic
import Theorems.Thm_BKAR_AcyclicEdgeSetData_inSameComponent_iff_exists_isSimplePath


set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
open BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKARMirror
theorem _root_.solution
    (G : BKAR.Forest V) (u : G.EdgeParam → ℝ) (s : ℝ) (i j : V) :
    G.thresholdConnected u s i j ↔
      ∃ γ, BKAR.EdgePath.IsSimplePath (G.thresholdEdges u s) γ i j := by
  constructor
  · intro h
    rw [G.thresholdConnected_iff_thresholdForest_inSameComponent u s] at h
    exact
      (BKAR.AcyclicEdgeSetData.inSameComponent_iff_exists_isSimplePath
        (G.thresholdForest u s).acyclic).mp h
  · intro h
    rw [G.thresholdConnected_iff_thresholdForest_inSameComponent u s]
    exact
      (BKAR.AcyclicEdgeSetData.inSameComponent_iff_exists_isSimplePath
        (G.thresholdForest u s).acyclic).mpr h
end BKARMirror
