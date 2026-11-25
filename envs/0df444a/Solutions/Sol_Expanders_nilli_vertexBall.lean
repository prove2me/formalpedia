-- Prove2me | solution 1 for Expanders.nilli_vertexBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:59:09.840149+00:00
-- url     : https://prove2.me/submissions/5204a415-f419-4acb-9858-6c78e6465308

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
public import Theorems.Thm_Expanders_nilli_ball
public import Theorems.Thm_Expanders_vertexBall_level_le
public import Theorems.Thm_Expanders_vertexBall_out
public import Theorems.Thm_Expanders_vertexBall_step
public import Theorems.Thm_Expanders_vertexBall_parent

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {u : V} {k : ℕ}
namespace Expanders
theorem _root_.solution [DecidableRel G.Adj] {d : ℕ} (hd2 : 2 ≤ d) (hd : G.IsRegularOfDegree d)
    (u : V) (k : ℕ) :
    (2 * Real.sqrt (d - 1) - (2 * Real.sqrt (d - 1) - 1) / (k + 1)) *
        dotProduct (nilliVec (Real.sqrt (d - 1)) (vertexBall G u k) (fun v => G.dist u v - 1))
          (nilliVec (Real.sqrt (d - 1)) (vertexBall G u k) (fun v => G.dist u v - 1)) ≤
      dotProduct (nilliVec (Real.sqrt (d - 1)) (vertexBall G u k) (fun v => G.dist u v - 1))
        (G.adjMatrix ℝ *ᵥ
          nilliVec (Real.sqrt (d - 1)) (vertexBall G u k) (fun v => G.dist u v - 1)) :=
  nilli_ball G _ _ hd2 hd vertexBall_level_le vertexBall_out vertexBall_step
    (vertexBall_parent hd (by omega))
end Expanders
