-- Prove2me | solution 1 for Expanders.vertexBall_level_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:29:45.654433+00:00
-- url     : https://prove2.me/submissions/7383dfd0-aac1-4867-b3e4-337507acd9fa

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
public import Theorems.Thm_Expanders_mem_vertexBall

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {u : V} {k : ℕ}
namespace Expanders
theorem _root_.solution : ∀ v ∈ vertexBall G u k, G.dist u v - 1 ≤ k := by
  intro v hv
  have := (mem_vertexBall.mp hv).2
  omega
end Expanders
