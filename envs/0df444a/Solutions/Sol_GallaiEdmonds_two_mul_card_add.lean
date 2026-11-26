-- Prove2me | solution 1 for GallaiEdmonds.two_mul_card_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:15:04.3843+00:00
-- url     : https://prove2.me/submissions/71ba482d-9f53-4d62-bb4b-96863ecd3978

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Theorems.Thm_GallaiEdmonds_setA_eq
public import Theorems.Thm_GallaiEdmonds_comps_setD
public import Theorems.Thm_GallaiEdmonds_IsBarrier_eq
public import Theorems.Thm_GallaiEdmonds_exists_minBarrier
public import Theorems.Thm_GallaiEdmonds_natCard_components_eq
public import Theorems.Thm_GallaiEdmonds_ncard_verts_eq_two_mul


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {M : G.Subgraph} (hM : IsMaximumMatching G M) :
    2 * M.edgeSet.ncard + Nat.card (G.induce (setD G)).ConnectedComponent =
      Nat.card V + (setA G).ncard := by
  obtain ⟨U, hU⟩ := exists_minBarrier G
  have heq := hU.1.eq hM.1 hM.2
  rw [ncard_verts_eq_two_mul hM.1] at heq
  rw [setA_eq G hU, natCard_components_eq, comps_setD G hU]
  exact heq
end GallaiEdmonds
