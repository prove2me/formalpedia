-- Prove2me | solution 1 for ChromaticReconstruction.coeff_chromSymm_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:21:30.076695+00:00
-- url     : https://prove2.me/submissions/b4777ba5-fdaf-4f35-9fee-3008d5fdcdbc

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Definitions.Def_RequestProject_ChromCoeff
import Theorems.Thm_ChromaticReconstruction_edges_not_diag
import Theorems.Thm_ChromaticReconstruction_coeff_chromSymm
import Theorems.Thm_ChromaticReconstruction_compType_pair
import Theorems.Thm_ChromaticReconstruction_eq_pair_of_compType
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
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
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (G : SimpleGraph V) :
    coeff (Multiset.toFinsupp (2 ::ₘ Multiset.replicate (Fintype.card V - 2) 1)) (chromSymm G) =
      - (G.edgeFinset.card : ℚ) := by
  rw [coeff_chromSymm]
  have : G.edgeFinset.powerset.filter (fun A : Finset (Sym2 V) =>
      compType (A : Set (Sym2 V)) = 2 ::ₘ Multiset.replicate (Fintype.card V - 2) 1) =
      G.edgeFinset.map ⟨fun e => {e}, singleton_injective⟩ := by
    ext A
    simp only [mem_filter, mem_powerset, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hA, h⟩
      obtain ⟨u, v, _, rfl⟩ := eq_pair_of_compType (edges_not_diag G hA) h
      exact ⟨s(u, v), hA (mem_singleton_self _), rfl⟩
    · rintro ⟨e, he, rfl⟩
      refine ⟨singleton_subset_iff.2 he, ?_⟩
      induction e using Sym2.ind with
      | _ u v =>
        have huv : u ≠ v := by
          intro h; subst h
          exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.1 he) (by simp)
        rw [coe_singleton]
        exact compType_pair huv
  rw [this, sum_map]
  simp
end ChromaticReconstruction
