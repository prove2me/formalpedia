-- Prove2me | solution 1 for ChromaticReconstruction.extEdges_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:21:12.970797+00:00
-- url     : https://prove2.me/submissions/95273b6d-5ed0-4e92-8c5b-f56346de1397

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_mem_extEdges_inl_inl
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}
namespace ChromaticReconstruction
theorem _root_.solution (l0 : Σ i, Fin (m i)) : Function.Injective (extEdges m l0) := by
  intro F F' h
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [← mem_extEdges_inl_inl (m := m) (l0 := l0), ← mem_extEdges_inl_inl (m := m) (l0 := l0),
      h]
end ChromaticReconstruction
