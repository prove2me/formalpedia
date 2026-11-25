-- Prove2me | solution 1 for Expanders.dist_triangle_of_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:19:54.361824+00:00
-- url     : https://prove2.me/submissions/5e9e8386-0c61-4966-90c3-f62f78da2880

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
theorem _root_.solution {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.dist u w ≤ G.dist u v + G.dist v w := by
  obtain ⟨p, hp⟩ := huv.exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := hvw.exists_walk_length_eq_dist
  have := dist_le (p.append q)
  simpa [Walk.length_append, hp, hq] using this
end Expanders
