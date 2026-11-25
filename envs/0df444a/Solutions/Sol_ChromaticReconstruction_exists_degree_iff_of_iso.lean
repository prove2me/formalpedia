-- Prove2me | solution 1 for ChromaticReconstruction.exists_degree_iff_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:29:42.632799+00:00
-- url     : https://prove2.me/submissions/1ada89e9-b6e4-4cee-8377-ad8b6a404295

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_CountingLower

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) (d : ℕ) :
    (∃ v, G.degree v = d) ↔ (∃ w, H.degree w = d) := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨e v, by rw [SimpleGraph.Iso.degree_eq]; exact hv⟩
  · rintro ⟨w, hw⟩
    exact ⟨e.symm w, by rw [← hw, ← SimpleGraph.Iso.degree_eq e, e.apply_symm_apply]⟩
end ChromaticReconstruction
