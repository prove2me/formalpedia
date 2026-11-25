-- Prove2me | solution 1 for ChromaticReconstruction.coeff_chromSymm_replicate_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:20:03.174873+00:00
-- url     : https://prove2.me/submissions/afb2b340-f4bd-4af6-baa9-d759631ddffb

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Definitions.Def_RequestProject_ChromCoeff
import Theorems.Thm_ChromaticReconstruction_edges_not_diag
import Theorems.Thm_ChromaticReconstruction_coeff_chromSymm
import Theorems.Thm_ChromaticReconstruction_compType_empty
import Theorems.Thm_ChromaticReconstruction_eq_empty_of_compType_replicate
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
theorem _root_.solution (G : SimpleGraph V) (s : ℕ) :
    coeff (Multiset.toFinsupp (Multiset.replicate s 1)) (chromSymm G) =
      if s = Fintype.card V then 1 else 0 := by
  rw [coeff_chromSymm]
  have : G.edgeFinset.powerset.filter (fun A : Finset (Sym2 V) =>
      compType (A : Set (Sym2 V)) = Multiset.replicate s 1) =
      if s = Fintype.card V then {∅} else ∅ := by
    ext A
    simp only [mem_filter, mem_powerset]
    constructor
    · rintro ⟨hA, h⟩
      have h0 := eq_empty_of_compType_replicate (edges_not_diag G hA) h
      subst h0
      rw [coe_empty, compType_empty] at h
      have := congrArg Multiset.card h
      simp only [Multiset.card_replicate] at this
      simp [this]
    · intro h
      split_ifs at h with hs
      · rw [mem_singleton] at h
        subst h hs
        exact ⟨empty_subset _, by rw [coe_empty, compType_empty]⟩
      · simp at h
  rw [this]
  split_ifs <;> simp
end ChromaticReconstruction
