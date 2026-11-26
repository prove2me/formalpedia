-- Prove2me | solution 1 for BKAR.Forest.empty_activeEdgePartialSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:50.604094+00:00
-- url     : https://prove2.me/submissions/41c8aeb6-b899-4baf-8713-0b36717f6d47

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_empty_interpWithFill


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (u : (Forest.empty V).EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) :
    (Forest.empty V).activeEdgePartialSum u ρ t =
      Finset.sum (Finset.univ : Finset (Edge V))
        (fun e => partialDeriv e ρ (constantConfig t)) := by
  rw [activeEdgePartialSum, empty_activeEdges, Forest.empty_interpWithFill u t]
end BKAR.Forest
