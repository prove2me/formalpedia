-- Prove2me | solution 1 for Csg.MatrixGame.abs_value_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:38:43.469479+00:00
-- url     : https://prove2.me/submissions/837457b9-1b8e-47ed-9ed6-01dd11a41f71

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
import Theorems.Thm_Csg_MatrixGame_value_le_add_of_forall_le

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
namespace Csg.MatrixGame
theorem _root_.solution {G G' : MatrixGame I J} {ε : ℝ}
    (h : ∀ i j, |G'.A i j - G.A i j| ≤ ε) : |G'.value - G.value| ≤ ε := by
  have hub : ∀ i j, G'.A i j ≤ G.A i j + ε := fun i j => by linarith [(abs_le.mp (h i j)).2]
  have hlb : ∀ i j, G.A i j ≤ G'.A i j + ε := fun i j => by linarith [(abs_le.mp (h i j)).1]
  have h1 : G'.value ≤ G.value + ε := value_le_add_of_forall_le hub
  have h2 : G.value ≤ G'.value + ε := value_le_add_of_forall_le hlb
  exact abs_le.mpr ⟨by linarith, by linarith⟩
end Csg.MatrixGame
