-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleFour.MMSEP_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:36:05.792417+00:00
-- url     : https://prove2.me/submissions/6da60589-6b56-4e89-a593-7b7a01f8edb1

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_price_nonneg
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_price_nonneg
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_outSellAll_valid
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_outSellAll_equalProceeds
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_outKeepAll_valid
import Theorems.Thm_FairSelling_EqualProceedsExampleFour_outKeepAll_equalProceeds
import Theorems.Thm_FairSelling_MMSEP_le_PS
import Theorems.Thm_FairSelling_le_MMSEP


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleFour
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleFour
theorem _root_.solution (c : ℝ) (hc : 0 ≤ c) :
    MMSEP (N + 2) (fun _ => c) (price N) = max 1 c := by
  have hn : 0 < N + 2 := by omega
  have hv : ∀ g : Fin (N + 2), (0 : ℝ) ≤ c := fun _ => hc
  apply le_antisymm
  · have hPS : PS (N + 2) (fun _ => c) (price N) = max 1 c := by
      have hsum : ∑ g : Fin (N + 2), max (price N g) c = ((N : ℝ) + 2) * max 1 c := by
        simp [price]
      unfold PS
      rw [hsum]
      push_cast
      rw [mul_comm, mul_div_assoc, div_self (by positivity), mul_one]
    calc MMSEP (N + 2) (fun _ => c) (price N)
        ≤ PS (N + 2) (fun _ => c) (price N) :=
          MMSEP_le_PS _ _ hn hv (price_nonneg N)
      _ = max 1 c := hPS
  · refine max_le ?_ ?_
    · refine le_MMSEP _ _ hn hv (price_nonneg N)
        ⟨outSellAll N, outSellAll_valid N, outSellAll_equalProceeds N, fun j => ?_⟩
      simp [util, outSellAll]
    · refine le_MMSEP _ _ hn hv (price_nonneg N)
        ⟨outKeepAll N, outKeepAll_valid N, outKeepAll_equalProceeds N, fun j => ?_⟩
      simp [util, outKeepAll]
end FairSelling.EqualProceedsExampleFour
