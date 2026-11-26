-- Prove2me | solution 1 for GallaiEdmonds.setA_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:26.575836+00:00
-- url     : https://prove2.me/submissions/d9b21e13-bbb7-44f0-af9d-b428cef8a518

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Theorems.Thm_GallaiEdmonds_exists_maximum
public import Theorems.Thm_GallaiEdmonds_setD_eq
public import Theorems.Thm_GallaiEdmonds_IsBarrier_eq
public import Theorems.Thm_GallaiEdmonds_cc_eq_of_mem
public import Theorems.Thm_GallaiEdmonds_mem_cc_of_adj
public import Theorems.Thm_GallaiEdmonds_mem_cc_self
public import Theorems.Thm_GallaiEdmonds_step1


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {U : Set V} (hU : IsMinBarrier G U) : setA G = U := by
  ext a
  constructor
  · rintro ⟨haD, d, hdD, hadj⟩
    rw [setD_eq G hU] at haD hdD
    by_contra haU
    have had : a ∈ cc G Uᶜ d := mem_cc_of_adj (mem_cc_self hdD.1) haU hadj
    exact haD ⟨haU, by rw [cc_eq_of_mem had]; exact hdD.2⟩
  · intro hu
    obtain ⟨M, hM, hmax⟩ := exists_maximum G
    obtain ⟨h1a, -, -, -⟩ := step1 hM (hU.1.eq hM hmax)
    obtain ⟨x, hx, hxU, hodd⟩ := h1a a hu
    refine ⟨?_, x, ?_, (M.adj_sub hx).symm⟩
    · rw [setD_eq G hU]; exact fun h => h.1 hu
    · rw [setD_eq G hU]; exact ⟨hxU, hodd⟩
end GallaiEdmonds
