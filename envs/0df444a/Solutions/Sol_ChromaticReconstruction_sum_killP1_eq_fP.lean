-- Prove2me | solution 1 for ChromaticReconstruction.sum_killP1_eq_fP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:59:26.086191+00:00
-- url     : https://prove2.me/submissions/eea8bb9f-8abd-4d17-8016-28cc203f0e69

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
import Theorems.Thm_ChromaticReconstruction_killP1_mono
import Theorems.Thm_ChromaticReconstruction_prod_X_eq_mono
import Theorems.Thm_ChromaticReconstruction_X_mul_mono
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
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
variable {K : Type*} [Fintype K]
omit [Fintype K]
namespace ChromaticReconstruction
theorem _root_.solution (s : Finset K) (m : K → ℕ) (hm : ∀ i ∈ s, 1 ≤ m i) :
    ∑ i ∈ s, (m i : MvPolynomial ℕ ℚ) *
        killP1 (∏ j ∈ s, X ((m j + 1) - if i = j then 1 else 0)) =
      fP (s.val.map fun j => m j + 1) := by
  set W := s.val.map fun j => m j + 1 with hW
  have hW2 : ∀ x ∈ W, 2 ≤ x := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hx
    have := hm j hj
    omega
  have hterm : ∀ i ∈ s, (m i : MvPolynomial ℕ ℚ) *
      killP1 (∏ j ∈ s, X ((m j + 1) - if i = j then 1 else 0)) =
      (fun a => if 3 ≤ a then ((a - 1 : ℕ) : MvPolynomial ℕ ℚ) * mono (lowerAt W a) else 0)
        (m i + 1) := by
    intro i hi
    have hprod : ∏ j ∈ s, (X ((m j + 1) - if i = j then 1 else 0) : MvPolynomial ℕ ℚ) =
        mono (lowerAt W (m i + 1)) := by
      rw [← mul_prod_erase s _ hi, if_pos rfl,
        prod_congr rfl (fun j hj => by rw [if_neg (ne_of_mem_erase hj).symm, Nat.sub_zero]),
        prod_X_eq_mono, X_mul_mono]
      unfold lowerAt
      rw [hW, erase_val, Multiset.map_erase_of_mem _ _ hi]
    rw [hprod, killP1_mono]
    have hmi := hm i hi
    by_cases h1 : m i = 1
    · rw [if_pos (by unfold lowerAt; simp [h1])]
      simp [h1]
    · rw [if_neg]
      · show _ = if 3 ≤ m i + 1 then _ else _
        rw [if_pos (by omega)]
        simp
      · unfold lowerAt
        rw [Multiset.mem_cons, not_or]
        refine ⟨by omega, fun h => ?_⟩
        have := hW2 1 (Multiset.mem_of_mem_erase h)
        omega
  rw [sum_congr rfl hterm, Finset.sum_comp
    (fun a => if 3 ≤ a then ((a - 1 : ℕ) : MvPolynomial ℕ ℚ) * mono (lowerAt W a) else 0)
    (fun j => m j + 1)]
  unfold fP bigWeights
  rw [sum_filter, hW, Multiset.toFinset_map, val_toFinset]
  refine sum_congr rfl fun b _ => ?_
  have hc : #{a ∈ s | m a + 1 = b} = Multiset.count b (s.val.map fun j => m j + 1) := by
    rw [Multiset.count_map, card_def, filter_val]
    congr 1
    exact Multiset.filter_congr fun x _ => eq_comm
  rw [hc]
  split_ifs
  · rw [nsmul_eq_mul, ← hW]
    simp only [Nat.cast_mul, map_mul, map_natCast]
    ring
  · simp
end ChromaticReconstruction
