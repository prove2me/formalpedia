-- Prove2me | solution 1 for ChromaticReconstruction.coeff_psi_pderiv_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:27.795811+00:00
-- url     : https://prove2.me/submissions/bb335ec4-160b-445f-85c7-89d08325cc42

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2
import Theorems.Thm_ChromaticReconstruction_toFinsupp_pair_sub
import Theorems.Thm_ChromaticReconstruction_toFinsupp_pair_two
import Theorems.Thm_ChromaticReconstruction_coeff_pderiv_sub
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
variable {V W : Type*} [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution (q : ℕ) (hq : 1 ≤ q) (G : SimpleGraph V) (s : ℕ) :
    coeff ((Multiset.toFinsupp (Multiset.replicate s 1)).mapDomain (fun r => q * r))
      (psiQ q (pderiv 2 (chromSymm G))) =
      coeff (Multiset.toFinsupp (2 ::ₘ Multiset.replicate s 1)) (chromSymm G) := by
  rw [psiQ, coeff_rename_mapDomain _ (fun a b h => Nat.eq_of_mul_eq_mul_left (by omega) h),
    ← toFinsupp_pair_sub, coeff_pderiv_sub _ _ _ (by rw [toFinsupp_pair_two]),
    toFinsupp_pair_two]
  simp
end ChromaticReconstruction
