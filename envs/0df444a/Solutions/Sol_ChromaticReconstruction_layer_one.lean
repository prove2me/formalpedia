-- Prove2me | solution 1 for ChromaticReconstruction.layer_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:15:54.176274+00:00
-- url     : https://prove2.me/submissions/5413e8d2-fc67-46d6-864b-aeb122a843c5

import Definitions.Def_RequestProject_Recovery
import Definitions.Def_RequestProject_RecoveryThm
import Theorems.Thm_ChromaticReconstruction_layer_tree
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_masterTerm_univ
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_theta_mk
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr
attribute [local simp] ChromaticReconstruction.pairMS_mk
attribute [local simp] ChromaticReconstruction.pairSum_mk
attribute [local simp] ChromaticReconstruction.theta_mk



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
namespace ChromaticReconstruction
theorem _root_.solution (hS : S.IsTree) (hm : ∀ i, 1 ≤ m i) (hn : 3 ≤ Fintype.card K + ∑ i, m i) :
    homogeneousComponent 1 (phi (leafExt S m)) =
      C ((-1 : ℚ) ^ (Fintype.card K + ∑ i, m i) * (∑ i, m i : ℕ)) *
        X (Fintype.card K + ∑ i, m i - 1) := by
  rw [layer_tree S m hS hm]
  have hE := hS.card_edgeFinset
  have hfilt : S.edgeFinset.powerset.filter
      (fun F : Finset (Sym2 K) => Fintype.card K = 1 + F.card) = {S.edgeFinset} := by
    ext F
    simp only [mem_filter, mem_powerset, mem_singleton]
    constructor
    · rintro ⟨hF, h⟩
      exact eq_of_subset_of_card_le hF (by omega)
    · rintro rfl
      exact ⟨subset_refl _, by omega⟩
  have hN : 1 ≤ ∑ i, m i := by
    obtain ⟨v⟩ := hS.1.nonempty
    exact le_trans (hm v) (single_le_sum (fun i _ => Nat.zero_le _) (mem_univ v))
  rw [hfilt, sum_singleton, masterTerm_univ S m hS.1 (by omega)]
  have hpow : ((-1 : MvPolynomial ℕ ℚ)) ^ ((∑ i, m i) - 1 + S.edgeFinset.card) =
      C ((-1 : ℚ) ^ (Fintype.card K + ∑ i, m i)) := by
    rw [map_pow, map_neg, map_one]
    have : (∑ i, m i) - 1 + S.edgeFinset.card + 2 = Fintype.card K + ∑ i, m i := by omega
    rw [← this, pow_add (-1 : MvPolynomial ℕ ℚ) (∑ i, m i - 1 + S.edgeFinset.card) 2, neg_one_sq, mul_one]
  rw [hpow, map_mul, map_natCast]
  ring
end ChromaticReconstruction
