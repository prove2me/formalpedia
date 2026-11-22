-- Prove2me | solution 1 for Csg.MatrixGame.value_le_add_of_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:36:19.813651+00:00
-- url     : https://prove2.me/submissions/4d0e1b18-dada-444c-9947-046ce5f98f7f

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
import Theorems.Thm_Csg_MatrixGame_value_mono
import Theorems.Thm_Csg_MatrixGame_value_add_const

set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
namespace Csg.MatrixGame
theorem _root_.solution {G G' : MatrixGame I J} {ε : ℝ}
    (h : ∀ i j, G'.A i j ≤ G.A i j + ε) : G'.value ≤ G.value + ε := by
  have hmono : G'.value ≤ (⟨fun i j => G.A i j + ε⟩ : MatrixGame I J).value :=
    value_mono (G := G') (G' := (⟨fun i j => G.A i j + ε⟩ : MatrixGame I J)) h
  have hHeq : (⟨fun i j => G.A i j + ε⟩ : MatrixGame I J).value = G.value + ε :=
    value_add_const (G := G) (G' := (⟨fun i j => G.A i j + ε⟩ : MatrixGame I J)) ε
      (fun _ _ => rfl)
  linarith
end Csg.MatrixGame
