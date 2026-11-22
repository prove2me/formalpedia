-- Prove2me | solution 1 for Csg.MatrixGame.value_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:31:36.458933+00:00
-- url     : https://prove2.me/submissions/34042aea-d6b8-4a5d-bb30-7d76a991bb85

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
import Theorems.Thm_Csg_MatrixGame_optimalRow_mem
import Theorems.Thm_Csg_MatrixGame_optimalCol_mem
import Theorems.Thm_Csg_MatrixGame_value_row_optimal
import Theorems.Thm_Csg_MatrixGame_value_col_optimal
import Theorems.Thm_Csg_MatrixGame_payoff_mono

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
namespace Csg.MatrixGame
theorem _root_.solution {G G' : MatrixGame I J} (h : ∀ i j, G.A i j ≤ G'.A i j) :
    G.value ≤ G'.value :=
  calc G.value ≤ G.payoff G'.optimalRow G.optimalCol :=
        G.value_row_optimal G'.optimalRow G'.optimalRow_mem
    _ ≤ G'.payoff G'.optimalRow G.optimalCol :=
        payoff_mono h G'.optimalRow_mem.1 G.optimalCol_mem.1
    _ ≤ G'.value := G'.value_col_optimal G.optimalCol G.optimalCol_mem
end Csg.MatrixGame
