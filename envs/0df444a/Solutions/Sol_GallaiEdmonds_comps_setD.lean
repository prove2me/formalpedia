-- Prove2me | solution 1 for GallaiEdmonds.comps_setD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:27.49717+00:00
-- url     : https://prove2.me/submissions/1dd05591-40f1-46a2-a0be-367cd4b0e272

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Theorems.Thm_GallaiEdmonds_oddPart_closed
public import Theorems.Thm_GallaiEdmonds_oddPart_subset
public import Theorems.Thm_GallaiEdmonds_setD_eq
public import Theorems.Thm_GallaiEdmonds_comps_eq_cc
public import Theorems.Thm_GallaiEdmonds_comps_nonempty
public import Theorems.Thm_GallaiEdmonds_comps_of_closed
public import Theorems.Thm_GallaiEdmonds_comps_subset


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {U : Set V} (hU : IsMinBarrier G U) :
    comps G (setD G) = oddComps G Uᶜ := by
  rw [setD_eq G hU, comps_of_closed (oddPart_subset G U) (oddPart_closed G U)]
  ext K
  constructor
  · rintro ⟨hK, hsub⟩
    obtain ⟨y, hy⟩ := comps_nonempty hK
    refine ⟨hK, ?_⟩
    rw [comps_eq_cc hK hy]
    exact (hsub hy).2
  · rintro ⟨hK, hodd⟩
    exact ⟨hK, fun y hy => ⟨comps_subset hK hy, by rw [← comps_eq_cc hK hy]; exact hodd⟩⟩
end GallaiEdmonds
