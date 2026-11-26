-- Prove2me | solution 1 for GallaiEdmonds.compSet_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:27.059688+00:00
-- url     : https://prove2.me/submissions/a81e93a9-3591-4e84-826b-eb89914d1452

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Theorems.Thm_GallaiEdmonds_oddPart_closed
public import Theorems.Thm_GallaiEdmonds_oddPart_subset
public import Theorems.Thm_GallaiEdmonds_setD_eq
public import Theorems.Thm_GallaiEdmonds_IsBarrier_eq
public import Theorems.Thm_GallaiEdmonds_cc_eq_of_closed


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {U : Set V} (hU : IsMinBarrier G U) (x : V) (hx : x ∈ setD G) :
    compSet G ((G.induce (setD G)).connectedComponentMk ⟨x, hx⟩) = cc G Uᶜ x := by
  have h1 : compSet G ((G.induce (setD G)).connectedComponentMk ⟨x, hx⟩) = cc G (setD G) x := by
    ext y
    simp only [compSet, Set.mem_ofPred_eq, ConnectedComponent.eq, cc]
    constructor
    · rintro ⟨hy, r⟩; exact ⟨hx, hy, r.symm⟩
    · rintro ⟨_, hy, r⟩; exact ⟨hy, r.symm⟩
  have hxO : x ∈ oddPart G U := setD_eq G hU ▸ hx
  rw [h1, setD_eq G hU, cc_eq_of_closed (oddPart_subset G U) (oddPart_closed G U) hxO]
end GallaiEdmonds
