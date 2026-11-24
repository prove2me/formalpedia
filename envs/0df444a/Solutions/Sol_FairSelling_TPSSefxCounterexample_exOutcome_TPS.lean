-- Prove2me | solution 1 for FairSelling.TPSSefxCounterexample.exOutcome_TPS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:41:56.577272+00:00
-- url     : https://prove2.me/submissions/fef1b9ce-0bdb-4057-b503-1c007c7d258b

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSSefxExamples
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exThreshold
import Theorems.Thm_FairSelling_TPSSefxCounterexample_exOutcome_util

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.TPSSefxCounterexample
namespace FairSelling.TPSSefxCounterexample
theorem _root_.solution :
    ∀ i, ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 (exV i) exp ≤ util (exV i) exOutcome i := by
  intro i
  have h := exOutcome_util
  fin_cases i
  · show ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 exv exp ≤ util exv exOutcome 0
    rw [exThreshold, h.1]; norm_num
  · show ((2 : ℝ) / (2 * 2 - 1)) * TPS 2 exv exp ≤ util exv exOutcome 1
    rw [exThreshold, h.2]; norm_num
end FairSelling.TPSSefxCounterexample
