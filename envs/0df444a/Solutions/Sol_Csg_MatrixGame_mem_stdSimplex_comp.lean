-- Prove2me | solution 1 for Csg.MatrixGame.mem_stdSimplex_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:07.769802+00:00
-- url     : https://prove2.me/submissions/9694f7f0-a50b-42c8-b094-64ddaaed2cea

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']
omit [Nonempty I] [DecidableEq I] [Nonempty I'] [DecidableEq I']
namespace Csg.MatrixGame
theorem _root_.solution (e : I' ≃ I) {x : I → ℝ} (hx : x ∈ stdSimplex ℝ I) :
    x ∘ ⇑e ∈ stdSimplex ℝ I' := by
  obtain ⟨hnonneg, hsum⟩ := hx
  exact ⟨fun i' => hnonneg (e i'), (Equiv.sum_comp e x).trans hsum⟩
end Csg.MatrixGame
