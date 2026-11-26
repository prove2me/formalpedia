-- Prove2me | solution 1 for GallaiEdmonds.closed_iUnion_comps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:03:18.662461+00:00
-- url     : https://prove2.me/submissions/ab86beca-ac47-4b1e-9b26-61c597bd1033

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_comps_closed

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution {Q : Set (Set V)} (hQ : Q ⊆ comps G W) : Closed G W (⋃₀ Q) := by
  rintro y ⟨K, hKQ, hyK⟩ z hz hadj
  exact ⟨K, hKQ, comps_closed (hQ hKQ) y hyK z hz hadj⟩
end GallaiEdmonds
