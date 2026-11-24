-- Prove2me | solution 1 for FairSelling.lemmaFour_of_no_undervaluation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:01:07.878403+00:00
-- url     : https://prove2.me/submissions/9fcdb465-3d50-44cc-a8ef-2c05933daea8

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_four_thr_le_vbarSum_univ
import Theorems.Thm_FairSelling_MMS2_cash_of_total
import Theorems.Thm_FairSelling_MMS_nonneg
import Theorems.Thm_FairSelling_vbarSum_sdiff
import Theorems.Thm_FairSelling_vbarSum_union


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p)
    (K S : Finset G) (m : ℝ) (hKS : Disjoint K S) (hmS : m ≤ ∑ g ∈ S, p g)
    (hS : vbarSum w p S ≤ ∑ g ∈ S, p g)
    (hrej : vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p) :
    (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ S)) w)
      (cashPrice (Finset.univ \ (K ∪ S)) p ((∑ g ∈ S, p g) - m)) := by
  classical
  have hτ : 0 ≤ (3 / 4 : ℝ) * MMS 3 w p := by
    have := MMS_nonneg (n := 3) (by norm_num) w p hw hp
    linarith
  refine MMS2_cash_of_total w p hw hp (Finset.univ \ (K ∪ S)) ((∑ g ∈ S, p g) - m)
    ((3 / 4 : ℝ) * MMS 3 w p) (by linarith) hτ (fun g _ => (hnobig g).le) ?_
  have hsdiff := vbarSum_sdiff w p (Finset.subset_univ (K ∪ S))
  have hunion := vbarSum_union w p hKS
  have htot := four_thr_le_vbarSum_univ w p hw hp
  rw [hsdiff, hunion]
  linarith
end FairSelling
