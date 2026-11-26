-- Prove2me | solution 1 for GallaiEdmonds.setD_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:12:22.247998+00:00
-- url     : https://prove2.me/submissions/b8f5ab24-936b-4ff7-8e4a-df4b37a9f952

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Theorems.Thm_GallaiEdmonds_exists_maximum
public import Theorems.Thm_GallaiEdmonds_IsBarrier_eq
public import Theorems.Thm_GallaiEdmonds_exists_max_missing
public import Theorems.Thm_GallaiEdmonds_step1


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {U : Set V} (hU : IsMinBarrier G U) : setD G = oddPart G U := by
  ext v
  constructor
  · rintro ⟨M, ⟨hM, hmax⟩, hv⟩
    obtain ⟨h1a, -, -, h1d⟩ := step1 hM (hU.1.eq hM hmax)
    have hvU : v ∉ U := fun hvU => by
      obtain ⟨x, hx, -⟩ := h1a v hvU
      exact hv (M.edge_vert hx)
    refine ⟨hvU, ?_⟩
    by_contra hodd
    obtain ⟨w, -, hw⟩ := h1d v hvU (Nat.not_odd_iff_even.mp hodd)
    exact hv (M.edge_vert hw)
  · intro hv
    obtain ⟨M, hM, hmax⟩ := exists_maximum G
    obtain ⟨M', hM', hmax', hvM'⟩ := exists_max_missing hU hM hmax hv
    exact ⟨M', ⟨hM', hmax'⟩, hvM'⟩
end GallaiEdmonds
