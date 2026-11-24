-- Prove2me | solution 1 for FairSelling.EqualProceedsExampleThree.MMS_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:33:46.940702+00:00
-- url     : https://prove2.me/submissions/61a836ee-4fd9-43fa-bb9a-c4f2edd7ca79

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_val_nonneg
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_price_nonneg
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_PS_eq
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_out1_valid
import Theorems.Thm_FairSelling_EqualProceedsExampleThree_util_out1
import Theorems.Thm_FairSelling_MMSset_bddAbove
import Theorems.Thm_FairSelling_MMSset_le_PS
import Theorems.Thm_FairSelling_MMSset_nonempty


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open FairSelling.EqualProceedsExampleThree
variable (N : ℕ)
namespace FairSelling.EqualProceedsExampleThree
theorem _root_.solution : MMS (N + 1) (val N) (price N) = 1 := by
  apply le_antisymm
  · refine csSup_le (MMSset_nonempty _ _) fun r hr => ?_
    have := MMSset_le_PS (val N) (price N) (Nat.succ_pos N) (val_nonneg N) (price_nonneg N) hr
    rwa [PS_eq] at this
  · refine le_csSup (MMSset_bddAbove _ _ (Nat.succ_pos N) (val_nonneg N) (price_nonneg N)) ?_
    exact ⟨out1 N, out1_valid N, fun j => (util_out1 N j).ge⟩
end FairSelling.EqualProceedsExampleThree
