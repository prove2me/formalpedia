-- Prove2me | solution 1 for BKAR.Forest.activeEdgePartialSum_empty_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:38.880162+00:00
-- url     : https://prove2.me/submissions/6ffdbb94-c978-4545-90f7-4cc6ae50489e

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (hF : F.activeEdges = ∅)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) :
    F.activeEdgePartialSum u ρ t = 0 := by
  rw [activeEdgePartialSum, hF]
  exact Finset.sum_empty
end BKAR.Forest
