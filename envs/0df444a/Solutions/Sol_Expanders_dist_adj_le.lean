-- Prove2me | solution 1 for Expanders.dist_adj_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:08:54.908242+00:00
-- url     : https://prove2.me/submissions/1149cf56-4e8a-46e4-a7a7-9e75b2bab5f5

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} {G : SimpleGraph V}
namespace Expanders
theorem _root_.solution {u v w : V} (huv : G.Reachable u v) (hvw : G.Adj v w) :
    G.dist u w ≤ G.dist u v + 1 := by
  obtain ⟨p, hp⟩ := huv.exists_walk_length_eq_dist
  have := dist_le (p.concat hvw)
  simpa [Walk.length_concat, hp] using this
end Expanders
