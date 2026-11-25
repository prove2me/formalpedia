-- Prove2me | solution 1 for ChromaticReconstruction.adj_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:58:59.47977+00:00
-- url     : https://prove2.me/submissions/7f4abea0-20e0-43bb-b425-718989d285eb

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
import Theorems.Thm_ChromaticReconstruction_sum_card_nbr_weight
import Theorems.Thm_ChromaticReconstruction_eq_of_count_eq_one
import Theorems.Thm_ChromaticReconstruction_adj_map_of_repeated
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
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K K' : Type*} [Fintype K] [Fintype K'] {S : SimpleGraph K} {S' : SimpleGraph K'}
  {w : K → ℕ} {w' : K' → ℕ}
namespace ChromaticReconstruction
theorem _root_.solution (hS : S.Connected) (hk : 3 ≤ Fintype.card K) (hMI : MIso S w)
    (hW : wts w = wts w') (hE : edgeTypes S w = edgeTypes S' w') (φ : K ≃ K')
    (hkey : ∀ x, keyOf S' w' (φ x) = keyOf S w x) {x y : K} (hxy : S.Adj x y) :
    S'.Adj (φ x) (φ y) := by
  have hw : ∀ x, w' (φ x) = w x := fun x => congrArg Prod.fst (hkey x)
  by_cases hx : Multiset.count (w x) (wts w) = 1
  · by_cases hy : Multiset.count (w y) (wts w) = 1
    · have hab : w x ≠ w y := fun h => S.ne_of_adj hxy (eq_of_count_eq_one hx rfl h.symm)
      have h1 := sum_card_nbr_weight S w hab
      have h2 := sum_card_nbr_weight S' w' hab
      rw [← hE, ← h1] at h2
      have hpos : 0 < ∑ x' ∈ univ.filter (fun x' => w x' = w x),
          #{y' ∈ S.neighborFinset x' | w y' = w y} := by
        refine lt_of_lt_of_le (card_pos.2 ⟨y, ?_⟩)
          (single_le_sum (f := fun x' => #{y' ∈ S.neighborFinset x' | w y' = w y})
            (fun _ _ => Nat.zero_le _) (by simp : x ∈ univ.filter (fun x' => w x' = w x)))
        simp [hxy]
      rw [← h2] at hpos
      obtain ⟨x'', hx'', hpos''⟩ : ∃ x'' ∈ univ.filter (fun x' => w' x' = w x),
          0 < #{y' ∈ S'.neighborFinset x'' | w' y' = w y} := by
        by_contra hcon
        push_neg at hcon
        rw [sum_eq_zero (fun i hi => Nat.eq_zero_of_le_zero (hcon i hi))] at hpos
        exact lt_irrefl 0 hpos
      obtain ⟨y'', hy''⟩ := card_pos.1 hpos''
      simp only [mem_filter, mem_univ, true_and] at hx'' hy''
      rw [hW] at hx hy
      have e1 : x'' = φ x := eq_of_count_eq_one hx hx'' (hw x)
      have e2 : y'' = φ y := eq_of_count_eq_one hy hy''.2 (hw y)
      rw [← e1, ← e2]
      exact (S'.mem_neighborFinset _ _).1 hy''.1
    · exact (adj_map_of_repeated hS hk hMI hW φ hkey hxy.symm hy).symm
  · exact adj_map_of_repeated hS hk hMI hW φ hkey hxy hx
end ChromaticReconstruction
