-- Prove2me | solution 1 for DeletedPrimes.intervalIntegrable_err
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:14:07.42516+00:00
-- url     : https://prove2.me/submissions/c1ee112e-86bd-4910-b70b-ce177d4b8333

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_intervalIntegrable_count

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) (a b : ℝ) :
    IntervalIntegrable (err S) volume a b := by
  have h2 : IntervalIntegrable (fun x : ℝ => density S * x) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable a b
  exact (intervalIntegrable_count S a b).sub h2
end DeletedPrimes
