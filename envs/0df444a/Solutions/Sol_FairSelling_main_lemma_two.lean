-- Prove2me | solution 1 for FairSelling.main_lemma_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:40:41.71268+00:00
-- url     : https://prove2.me/submissions/fe6dfc05-45a9-4304-9863-9953ed646bfa

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_MMS_nonneg
import Theorems.Thm_FairSelling_pure_reduction
import Theorems.Thm_FairSelling_untouched_mms_part_reduction
import Theorems.Thm_FairSelling_paired_loss_bagfill_reduction

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (B : Finset G) (hloss : MainLemmaTwoLoss w p B) :
    (3/4) * MMS 3 w p ≤
      MMS 2 (restrictVal (Finset.univ \ B) w) (restrictVal (Finset.univ \ B) p) := by
  obtain ⟨hnobig, hcase⟩ | ⟨A, s, q, lost, j, k, g, hB, hcfg, hlj, hlk, hjk, hg⟩ | ⟨C, hC, hClo, hChi, hR⟩ := hloss;
  · exact pure_reduction w p hw hp hnobig B hcase;
  · have hfull := untouched_mms_part_reduction w p hw hp A s q hcfg lost j k hlj hlk hjk g hg
    have hM0 : 0 ≤ MMS 3 w p := MMS_nonneg (n := 3) (by decide) w p hw hp
    rw [hB]
    exact (by linarith : (3/4) * MMS 3 w p ≤ MMS 3 w p) |>.trans hfull;
  · exact paired_loss_bagfill_reduction w p hw hp _ _ hC hClo hChi hR
end FairSelling
