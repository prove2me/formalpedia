-- Prove2me | solution 1 for GallaiEdmonds.comps_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:04:06.317843+00:00
-- url     : https://prove2.me/submissions/6a70e0fe-a021-4fed-8d01-28b4bc8389b7

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents
public import Theorems.Thm_GallaiEdmonds_comps_subset
public import Theorems.Thm_GallaiEdmonds_comps_nonempty
public import Theorems.Thm_GallaiEdmonds_comps_eq_of_mem
public import Theorems.Thm_GallaiEdmonds_comps_closed
public import Theorems.Thm_GallaiEdmonds_comps_of_closed

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution {K : Set V} (hK : K ∈ comps G W) : comps G K = {K} := by
  rw [comps_of_closed (comps_subset hK) (comps_closed hK)]
  ext K'
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hK', hsub⟩
    obtain ⟨y, hy⟩ := comps_nonempty hK'
    exact comps_eq_of_mem hK' hK hy (hsub hy)
  · rintro rfl; exact ⟨hK, le_rfl⟩
end GallaiEdmonds
