-- Prove2me | solution 1 for ChromaticReconstruction.coeff_chromSymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:16:32.705138+00:00
-- url     : https://prove2.me/submissions/cc18283f-e20a-4940-ba10-0d663cb80716

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
import Definitions.Def_RequestProject_ChromCoeff
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_typeMonomial_eq_monomial
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
theorem _root_.solution (G : SimpleGraph V) (μ : Multiset ℕ) :
    coeff (Multiset.toFinsupp μ) (chromSymm G) =
      ∑ A ∈ G.edgeFinset.powerset.filter (fun A : Finset (Sym2 V) =>
        compType (A : Set (Sym2 V)) = μ), (-1) ^ A.card := by
  unfold chromSymm
  rw [coeff_sum, sum_filter]
  refine sum_congr rfl fun A _ => ?_
  have hc : ((-1 : MvPolynomial ℕ ℚ) ^ A.card) = C ((-1) ^ A.card) := by simp
  rw [hc, coeff_C_mul, typeMonomial_eq_monomial, coeff_monomial]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  split_ifs <;> simp
end ChromaticReconstruction
