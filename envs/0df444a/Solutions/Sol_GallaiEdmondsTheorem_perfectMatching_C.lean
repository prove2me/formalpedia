-- Prove2me | solution 1 for GallaiEdmondsTheorem.perfectMatching_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:17:51.183801+00:00
-- url     : https://prove2.me/submissions/2c8444dc-f727-4b2b-87c7-17fae82f8633

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Definitions.Def_BergeMatching_Solution
public import Theorems.Thm_GallaiEdmonds_perfectMatching_C


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmondsTheorem
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmondsTheorem
theorem _root_.solution [Finite V] : HasPerfectMatchingOn G (setC G) :=
  GallaiEdmonds.perfectMatching_C G
end GallaiEdmondsTheorem
