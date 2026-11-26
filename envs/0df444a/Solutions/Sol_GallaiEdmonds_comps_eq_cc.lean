-- Prove2me | solution 1 for GallaiEdmonds.comps_eq_cc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:00:35.997803+00:00
-- url     : https://prove2.me/submissions/ba340ea6-47e8-470e-a28c-e29f2b8ae2bf

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_cc_eq_of_mem

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution {K : Set V} (hK : K ∈ comps G W) (hy : y ∈ K) : K = cc G W y := by
  obtain ⟨x, -, rfl⟩ := hK; exact (cc_eq_of_mem hy).symm
end GallaiEdmonds
