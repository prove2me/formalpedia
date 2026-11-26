-- Prove2me | solution 1 for GallaiEdmondsTheorem.factorCritical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:17:19.125635+00:00
-- url     : https://prove2.me/submissions/c6419b82-bab0-408a-9b6a-cf265ec11d00

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_GallaiEdmonds_factorCritical


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmondsTheorem
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmondsTheorem
theorem _root_.solution [Finite V] (c : (G.induce (setD G)).ConnectedComponent) :
    ∀ v ∈ compSet G c, HasPerfectMatchingOn G (compSet G c \ {v}) :=
  GallaiEdmonds.factorCritical G c
end GallaiEdmondsTheorem
