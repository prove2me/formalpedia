-- Prove2me | solution 1 for ChromaticReconstruction.closeLeaves_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:20:51.651798+00:00
-- url     : https://prove2.me/submissions/747da4ee-8649-49f0-9042-1fee3d9d3781

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) {m : ℕ} (h : CloseLeaves G m) : CloseLeaves H m := by
  obtain ⟨u, v, huv, hu, hv, w, hw⟩ := h
  refine ⟨e u, e v, fun h => huv (e.injective h), by rwa [SimpleGraph.Iso.degree_eq],
    by rwa [SimpleGraph.Iso.degree_eq], w.map e.toHom, by rwa [SimpleGraph.Walk.length_map]⟩
end ChromaticReconstruction
