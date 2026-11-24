-- Prove2me | solution 1 for DeletedPrimes.moment_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:17:59.431178+00:00
-- url     : https://prove2.me/submissions/fa9babb1-6223-41e0-bc29-0610b15bf75e

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
import Theorems.Thm_DeletedPrimes_moment_exponent

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α b : ℝ} :
    Summable (fun n : ℕ => (n : ℝ) ^ (α - 1 - 2 * b)) ↔ α / 2 < b := by
  rw [Real.summable_nat_rpow, moment_exponent]
end DeletedPrimes
