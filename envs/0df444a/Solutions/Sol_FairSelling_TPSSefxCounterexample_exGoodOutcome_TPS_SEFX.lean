-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exGoodOutcome_TPS_SEFX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:42:42.849214+00:00
-- url     : https://prove2.me/submissions/366a6e23-574e-471b-9f65-11419f34152e

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_one
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_two
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exv_three
import Theorems.Thm_FairSelling_TPSSefxCounterexample_sum23
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exThreshold
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exGoodOutcome_valid
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exGoodOutcome_EF
import Theorems.Thm_FairSelling_SEFX_of_EF

attribute [local simp] FairSelling.TPSSefxCounterexample.exv_one
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_two
attribute [local simp] FairSelling.TPSSefxCounterexample.exv_three

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.TPSSefxCounterexample
namespace FairSelling.TPSSefxCounterexample
theorem _root_.solution :
    exGoodOutcome.Valid exp ∧
      (∀ i, ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 (exV i) exp ≤ util (exV i) exGoodOutcome i) ∧
      SEFX exV exp exGoodOutcome := by
  refine ⟨exGoodOutcome_valid, ?_, SEFX_of_EF exGoodOutcome_EF⟩
  intro i
  fin_cases i
  · show ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 exv exp ≤ util exv exGoodOutcome 0
    rw [exThreshold]
    show (20 : ℝ) ≤ (∑ g ∈ ({1} : Finset Gd), exv g) + 12
    norm_num [exv_one]
  · show ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 exv exp ≤ util exv exGoodOutcome 1
    rw [exThreshold]
    show (20 : ℝ) ≤ (∑ g ∈ ({2, 3} : Finset Gd), exv g) + 6
    rw [sum23]
    norm_num [exv_two, exv_three]
end FairSelling.TPSSefxCounterexample
