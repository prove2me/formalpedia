-- Prove2me | solution 1 for ChromaticReconstruction.mem_edgeSet_leafExt_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:17:08.566063+00:00
-- url     : https://prove2.me/submissions/b22775b2-162c-4d97-a719-064c0c296f8f

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}
omit [Fintype K]
namespace ChromaticReconstruction
theorem _root_.solution {l : Σ i, Fin (m i)} {w : K ⊕ Σ i, Fin (m i)}
    (h : s(.inr l, w) ∈ (leafExt S m).edgeSet) : w = .inl l.1 := by
  rw [SimpleGraph.mem_edgeSet] at h
  rcases w with a | l'
  · rw [leafExt_adj_inr_inl] at h; rw [h]
  · exact absurd h leafExt_adj_inr_inr
end ChromaticReconstruction
