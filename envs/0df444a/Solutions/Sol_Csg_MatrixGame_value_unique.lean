-- Prove2me | solution 1 for Csg.MatrixGame.value_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:43:01.375411+00:00
-- url     : https://prove2.me/submissions/13a5b8e1-cb44-4a4a-8a9b-29a34919d380

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
import Theorems.Thm_Csg_MatrixGame_optimalRow_mem
import Theorems.Thm_Csg_MatrixGame_optimalCol_mem
import Theorems.Thm_Csg_MatrixGame_value_row_optimal
import Theorems.Thm_Csg_MatrixGame_value_col_optimal

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
namespace Csg.MatrixGame
theorem _root_.solution {p : I → ℝ} {q : J → ℝ} (hp : p ∈ stdSimplex ℝ I) (hq : q ∈ stdSimplex ℝ J)
    (hrow : ∀ p' ∈ stdSimplex ℝ I, G.payoff p q ≤ G.payoff p' q)
    (hcol : ∀ q' ∈ stdSimplex ℝ J, G.payoff p q' ≤ G.payoff p q) :
    G.payoff p q = G.value := by
  apply le_antisymm
  · calc G.payoff p q ≤ G.payoff G.optimalRow q := hrow G.optimalRow G.optimalRow_mem
      _ ≤ G.value := G.value_col_optimal q hq
  · calc G.value ≤ G.payoff p G.optimalCol := G.value_row_optimal p hp
      _ ≤ G.payoff p q := hcol G.optimalCol G.optimalCol_mem
end Csg.MatrixGame
