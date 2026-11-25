-- Prove2me | solution 1 for Expanders.vertexBall_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:15.847508+00:00
-- url     : https://prove2.me/submissions/d213a4d6-41da-490f-a34e-37d275bb58e4

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
public import Theorems.Thm_Expanders_dist_adj_le
public import Theorems.Thm_Expanders_mem_vertexBall

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {u : V} {k : ℕ}
namespace Expanders
theorem _root_.solution : ∀ v ∈ vertexBall G u k, ∀ w ∈ vertexBall G u k, G.Adj v w →
    G.dist u w - 1 ≤ G.dist u v - 1 + 1 := by
  intro v hv w _ hvw
  have h1 := dist_adj_le (mem_vertexBall.mp hv).1 hvw
  omega
end Expanders
