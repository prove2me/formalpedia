-- Prove2me | solution 1 for FairSelling.vbarSum_sold_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:01:06.121383+00:00
-- url     : https://prove2.me/submissions/d6392969-e361-49f5-a8f1-40a0cf235ab3

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_MMS_nonneg


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (S : Finset G) (hcard : S.card ≤ 2)
    (hsmall : ∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p) :
    vbarSum w p S ≤ 2 * ((3 / 4 : ℝ) * MMS 3 w p) := by
  classical
  calc vbarSum w p S ≤ ∑ _g ∈ S, ((3 / 4 : ℝ) * MMS 3 w p) :=
        Finset.sum_le_sum (fun g _ => (hsmall g).le)
    _ = (S.card : ℝ) * ((3 / 4 : ℝ) * MMS 3 w p) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * ((3 / 4 : ℝ) * MMS 3 w p) := by
        have h1 : (S.card : ℝ) ≤ 2 := by exact_mod_cast hcard
        have h2 : (0 : ℝ) ≤ (3 / 4 : ℝ) * MMS 3 w p := by
          have := MMS_nonneg (n := 3) (by norm_num) w p hw hp
          linarith
        exact mul_le_mul_of_nonneg_right h1 h2
end FairSelling
