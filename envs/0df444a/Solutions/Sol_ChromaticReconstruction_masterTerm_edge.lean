-- Prove2me | solution 1 for ChromaticReconstruction.masterTerm_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:52:11.566327+00:00
-- url     : https://prove2.me/submissions/2e9a9bab-d059-4b57-9416-9855346a1a83

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
import Theorems.Thm_ChromaticReconstruction_killP1_mono
import Theorems.Thm_ChromaticReconstruction_prod_X_eq_mono
import Theorems.Thm_ChromaticReconstruction_sum_killP1_eq_fP
import Theorems.Thm_ChromaticReconstruction_X_mul_mono
import Theorems.Thm_ChromaticReconstruction_compSets_pair
import Theorems.Thm_ChromaticReconstruction_killP1_X_of_ne
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
variable (S : SimpleGraph K) (m : K → ℕ)
namespace ChromaticReconstruction
theorem _root_.solution (hm : ∀ i, 1 ≤ m i) {e : Sym2 K} (he : e ∈ S.edgeFinset) :
    masterTerm m {e} = theta (weightMS m) (e.map fun i => m i + 1) := by
  induction e using Sym2.ind with
  | _ u v =>
  have huv : u ≠ v := S.ne_of_adj (by simpa using he)
  set T : Finset K := univ \ {u, v} with hT
  have hnot : ({u, v} : Finset K) ∉ T.image fun w => ({w} : Finset K) := by
    intro h
    obtain ⟨w, _, hwe⟩ := mem_image.1 h
    have h1 : u ∈ ({w} : Finset K) := hwe ▸ mem_insert_self u {v}
    have h2 : v ∈ ({w} : Finset K) := hwe ▸ mem_insert_of_mem (mem_singleton_self v)
    simp only [mem_singleton] at h1 h2
    exact huv (h1.trans h2.symm)
  have huT : u ∉ T := by simp [hT]
  have hvT : v ∉ T := by simp [hT]
  have hTm : ∀ i ∈ T, 1 ≤ m i := fun i _ => hm i
  have hW : weightMS m = (m u + 1) ::ₘ (m v + 1) ::ₘ T.val.map fun j => m j + 1 := by
    have : (univ : Finset K) = insert u (insert v T) := by
      ext x; by_cases hx : x = u <;> by_cases hx' : x = v <;> simp [hT, hx, hx']
    unfold weightMS
    rw [this, insert_val_of_notMem (by simp [huv, huT]), insert_val_of_notMem hvT]
    simp
  have hWT : weightMS m - {m u + 1, m v + 1} = T.val.map fun j => m j + 1 := by
    rw [hW, show ∀ (a b : ℕ) (M : Multiset ℕ), a ::ₘ b ::ₘ M = {a, b} + M by
      intro a b M; simp [Multiset.insert_eq_cons], add_tsub_cancel_left]
  have hbig : ∀ x ∈ T.val.map (fun j => m j + 1), 2 ≤ x := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Multiset.mem_map.1 hx
    have := hm j; omega
  have hmono : killP1 (mono (T.val.map fun j => m j + 1)) = mono (T.val.map fun j => m j + 1) := by
    rw [killP1_mono, if_neg]
    intro h; have := hbig 1 h; omega
  unfold masterTerm
  rw [coe_singleton, compSets_pair, ← hT]
  simp only [prod_insert hnot, prod_image (fun a _ b _ h => singleton_injective h),
    sum_singleton, mem_singleton, sum_pair huv]
  rw [← sum_sdiff (subset_univ ({u, v} : Finset K)), sum_pair huv, ← hT]
  have hpart1 : ∑ i ∈ T, (m i : MvPolynomial ℕ ℚ) * killP1 (X (m u + 1 + (m v + 1) -
      if i ∈ ({u, v} : Finset K) then 1 else 0) *
        ∏ x ∈ T, X (m x + 1 - if i = x then 1 else 0)) =
      X (m u + 1 + (m v + 1)) * fP (T.val.map fun j => m j + 1) := by
    rw [← sum_killP1_eq_fP T m hTm, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ∉ ({u, v} : Finset K) := by simpa [hT] using hi
    rw [if_neg hi', Nat.sub_zero, map_mul, killP1_X_of_ne (by omega)]
    ring
  have hrest : ∀ i ∈ ({u, v} : Finset K), ∏ x ∈ T, (X (m x + 1 - if i = x then 1 else 0) :
      MvPolynomial ℕ ℚ) = mono (T.val.map fun j => m j + 1) := by
    intro i hi
    rw [← prod_X_eq_mono]
    refine prod_congr rfl fun x hx => ?_
    have : i ≠ x := fun h => by
      subst h
      simp only [mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact huT hx
      · exact hvT hx
    rw [if_neg this, Nat.sub_zero]
  rw [hpart1, hrest u (by simp), hrest v (by simp), if_pos (by simp), if_pos (by simp),
    map_mul, killP1_X_of_ne (by have := hm u; have := hm v; omega), hmono]
  rw [Sym2.map_pair_eq, theta_mk]
  unfold thetaAB
  rw [hWT, ← X_mul_mono]
  have hc : ((m u + 1 + (m v + 1) - 2 : ℕ) : ℚ) = (m u : ℚ) + m v := by
    rw [show m u + 1 + (m v + 1) - 2 = m u + m v by omega]; push_cast; ring
  rw [hc, show m u + 1 + (m v + 1) - 1 = m u + 1 + (m v + 1) - 1 from rfl]
  simp only [map_add, map_natCast]
  ring
end ChromaticReconstruction
