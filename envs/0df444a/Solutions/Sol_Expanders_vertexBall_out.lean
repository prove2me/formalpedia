-- Prove2me | solution 1 for Expanders.vertexBall_out
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:02.034293+00:00
-- url     : https://prove2.me/submissions/a38c45ca-ed66-4acc-8ac1-05d354990566

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
theorem _root_.solution : ∀ v ∈ vertexBall G u k, ∀ w, G.Adj v w → w ∉ vertexBall G u k →
    G.dist u v - 1 = k := by
  intro v hv w hvw hw
  rw [mem_vertexBall] at hv hw
  have h1 := dist_adj_le hv.1 hvw
  have h2 : ¬ G.dist u w ≤ k + 1 := fun h' => hw ⟨hv.1.trans hvw.reachable, h'⟩
  omega
end Expanders
