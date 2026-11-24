-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.MMSEP_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:36:13.458457+00:00
-- url     : https://prove2.me/submissions/a5a08cb3-3b22-4c4f-aa7f-fa7bc80cc8c4

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
import Theorems.Thm_FairSelling_exists_kept_subset
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_val_nonneg
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_price_nonneg
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_out2_valid
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_out2_equalProceeds
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_util_out2
import Theorems.Thm_FairSelling_MMSEP_le
import Theorems.Thm_FairSelling_le_MMSEP


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleThree
theorem _root_.solution : MMSEP (N + 1) (val N) (price N) = 1 / ((N : ℝ) + 1) := by
  apply le_antisymm
  · refine MMSEP_le _ _ fun r hr => ?_
    obtain ⟨o, hvalid, hep, hguar⟩ := hr
    have hcard : ((Finset.univ : Finset (Fin (N + 1))) \ {(0 : Fin (N + 1))}).card
        < (Finset.univ : Finset (Fin (N + 1))).card := by
      have h : ((Finset.univ : Finset (Fin (N + 1))) \ {(0 : Fin (N + 1))}).card = N := by
        rw [Finset.card_sdiff]
        simp
      simp only [Finset.card_univ, Fintype.card_fin, h]
      omega
    obtain ⟨j, -, hj⟩ := exists_kept_subset o {(0 : Fin (N + 1))}
      ((Finset.univ : Finset (Fin (N + 1))) \ {(0 : Fin (N + 1))}) Finset.univ hvalid.2.1
      (fun j => Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _)) hcard
    have hvj : ∑ g ∈ o.kept j, val N g = 0 := by
      refine Finset.sum_eq_zero fun g hg => ?_
      have hg0 : g = 0 := Finset.mem_singleton.mp (hj hg)
      simp [val, hg0]
    have hle : ∑ g ∈ o.sold, price N g ≤ 1 := by
      calc ∑ g ∈ o.sold, price N g
          ≤ ∑ g : Fin (N + 1), price N g :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun g _ _ => price_nonneg N g)
        _ = 1 := by simp [price]
    have hmoney : o.money j ≤ 1 / ((N : ℝ) + 1) := by
      rw [hep j]
      have hcast : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      gcongr
    have hg := hguar j
    unfold util at hg
    rw [hvj] at hg
    linarith
  · refine le_MMSEP _ _ (Nat.succ_pos N) (val_nonneg N) (price_nonneg N) ?_
    exact ⟨out2 N, out2_valid N, out2_equalProceeds N, fun j => util_out2 N j⟩
end FairSelling.EqualProceedsExampleThree
