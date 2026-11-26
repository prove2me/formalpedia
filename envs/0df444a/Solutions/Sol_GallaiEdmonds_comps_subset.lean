-- Prove2me | solution 1 for GallaiEdmonds.comps_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:58:28.004802+00:00
-- url     : https://prove2.me/submissions/cf5d27f5-da7a-4a8d-af4c-8bcfefdd8035

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_cc_subset

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution {K : Set V} (hK : K ∈ comps G W) : K ⊆ W := by
  obtain ⟨x, -, rfl⟩ := hK; exact cc_subset
end GallaiEdmonds
