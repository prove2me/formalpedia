-- Prove2me | solution 1 for GallaiEdmonds.perfectMatching_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:28.135004+00:00
-- url     : https://prove2.me/submissions/510b28b4-fbb6-48ee-ae28-0f85710a1448

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Theorems.Thm_GallaiEdmonds_exists_maximum
public import Theorems.Thm_GallaiEdmonds_mem_setC_iff
public import Theorems.Thm_GallaiEdmonds_IsBarrier_eq
public import Theorems.Thm_GallaiEdmonds_cc_eq_of_mem
public import Theorems.Thm_GallaiEdmonds_cc_subset
public import Theorems.Thm_GallaiEdmonds_exists_minBarrier
public import Theorems.Thm_GallaiEdmonds_step1


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmonds
theorem _root_.solution [Finite V] : HasPerfectMatchingOn G (setC G) := by
  obtain ⟨U, hU⟩ := exists_minBarrier G
  obtain ⟨M, hM, hmax⟩ := exists_maximum G
  obtain ⟨-, -, -, h1d⟩ := step1 hM (hU.1.eq hM hmax)
  refine ⟨M.induce (setC G), ?_, rfl⟩
  intro w hw
  have hw' := (mem_setC_iff G hU w).1 hw
  obtain ⟨z, hz, hadj⟩ := h1d w hw'.1 hw'.2
  have hzC : z ∈ setC G :=
    (mem_setC_iff G hU z).2 ⟨cc_subset hz, by rw [cc_eq_of_mem hz]; exact hw'.2⟩
  exact ⟨z, ⟨hw, hzC, hadj⟩, fun z' h => hM.eq_of_adj_left h.2.2 hadj⟩
end GallaiEdmonds
