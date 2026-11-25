-- Prove2me | solution 1 for ChromaticReconstruction.leafExt_recovery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:22:40.897827+00:00
-- url     : https://prove2.me/submissions/8b555031-f04b-4aca-a11d-b54b222a5e29

import Definitions.Def_RequestProject_Recovery
import Definitions.Def_RequestProject_RecoveryThm
import Theorems.Thm_ChromaticReconstruction_layer_one
import Theorems.Thm_ChromaticReconstruction_layer_card
import Theorems.Thm_ChromaticReconstruction_layer_edges
import Theorems.Thm_ChromaticReconstruction_pairMS_le_weightMS
import Theorems.Thm_ChromaticReconstruction_weightMS_ge_two
import Theorems.Thm_ChromaticReconstruction_fP_injective
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_theta_independent
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
theorem _root_.solution {K' : Type*} [Fintype K'] {S : SimpleGraph K} {S' : SimpleGraph K'}
    (hS : S.IsTree) (hS' : S'.IsTree) {m : K → ℕ} {m' : K' → ℕ} (hm : ∀ i, 1 ≤ m i)
    (hm' : ∀ i, 1 ≤ m' i) (hn : 3 ≤ Fintype.card K + ∑ i, m i)
    (hn' : 3 ≤ Fintype.card K' + ∑ i, m' i) (h : phi (leafExt S m) = phi (leafExt S' m')) :
    Fintype.card K = Fintype.card K' ∧ weightMS m = weightMS m' ∧
      edgeTypes S (fun i => m i + 1) = edgeTypes S' (fun i => m' i + 1) := by
  have hNpos : 1 ≤ ∑ i, m i := by
    obtain ⟨v⟩ := hS.1.nonempty
    exact le_trans (hm v) (single_le_sum (fun i _ => Nat.zero_le _) (mem_univ v))
  have hm1 : (-1 : MvPolynomial ℕ ℚ) ≠ 0 := neg_ne_zero.2 one_ne_zero
  -- layer 1: the order and the number of leaves
  have h1 := congrArg (homogeneousComponent 1) h
  rw [layer_one S m hS hm hn, layer_one S' m' hS' hm' hn'] at h1
  have hc := congrArg (coeff (Finsupp.single (Fintype.card K + ∑ i, m i - 1) 1)) h1
  rw [coeff_C_mul, coeff_C_mul, coeff_X', coeff_X', if_pos rfl, mul_one] at hc
  have hne : ((-1 : ℚ) ^ (Fintype.card K + ∑ i, m i) * ((∑ i, m i : ℕ) : ℚ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast (by omega : (∑ i, m i) ≠ 0))
  have hnn : Fintype.card K + ∑ i, m i = Fintype.card K' + ∑ i, m' i := by
    by_contra hne'
    rw [if_neg (fun h => by have := Finsupp.single_left_injective one_ne_zero h; omega),
      mul_zero] at hc
    exact hne hc
  rw [if_pos (by rw [show Fintype.card K' + ∑ i, m' i - 1 = Fintype.card K + ∑ i, m i - 1 by
    omega]), ← hnn, mul_one] at hc
  have hN : ∑ i, m i = ∑ i, m' i := by
    have := mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hc
    exact_mod_cast this
  have hk : Fintype.card K = Fintype.card K' := by omega
  -- layer `k`: the weight multiset
  have h2 := congrArg (homogeneousComponent (Fintype.card K)) h
  rw [layer_card S m hS hm, hk, layer_card S' m' hS' hm', hN] at h2
  have hW : weightMS m = weightMS m' := by
    refine fP_injective (weightMS_ge_two m hm) (weightMS_ge_two m' hm') ?_
      (mul_left_cancel₀ (pow_ne_zero _ hm1) h2)
    simp [weightMS, hk]
  refine ⟨hk, hW, ?_⟩
  -- layer `k - 1`: the edge types
  by_cases hk2 : 2 ≤ Fintype.card K
  · have h3 := congrArg (homogeneousComponent (Fintype.card K - 1)) h
    rw [layer_edges S m hS hm hk2, hk, layer_edges S' m' hS' hm' (hk ▸ hk2), hN, hW] at h3
    refine theta_independent (weightMS_ge_two m' hm') _ _ ?_
      (mul_left_cancel₀ (pow_ne_zero _ hm1) h3)
    intro z hz
    rcases Multiset.mem_add.1 hz with hz | hz
    · unfold edgeTypes at hz
      obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hz
      rw [← hW]
      exact pairMS_le_weightMS S m he
    · unfold edgeTypes at hz
      obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hz
      exact pairMS_le_weightMS S' m' he
  · have hE := hS.card_edgeFinset
    have hE' := hS'.card_edgeFinset
    have e1 : S.edgeFinset = ∅ := card_eq_zero.1 (by omega)
    have e2 : S'.edgeFinset = ∅ := card_eq_zero.1 (by omega)
    simp [edgeTypes, e1, e2]
end ChromaticReconstruction
