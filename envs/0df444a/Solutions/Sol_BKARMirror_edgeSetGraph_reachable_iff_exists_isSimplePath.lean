-- Prove2me | solution 1 for BKARMirror.edgeSetGraph_reachable_iff_exists_isSimplePath
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:14:35.752801+00:00
-- url     : https://prove2.me/submissions/600b96f8-b471-48a4-b306-bdd52e85afd7

import Mathlib
import Definitions.Def_BKAR
import Definitions.Def_Audit_ForestFormula_SolutionBasic

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
open BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BKARMirror
theorem _root_.solution
    (S : Finset (Edge V)) (i j : V) :
    (BKAR.EdgePath.edgeSetGraph S).Reachable i j ↔
      ∃ γ, BKAR.EdgePath.IsSimplePath S γ i j := by
  constructor
  · rintro ⟨w⟩
    exact ⟨_, BKAR.EdgePath.Walk.toEdgePath_isSimplePath_of_isPath w.toPath.2⟩
  · rintro ⟨γ, hγ⟩
    rcases hγ.1.exists_walk with ⟨p, _⟩
    exact ⟨p⟩
end BKARMirror
