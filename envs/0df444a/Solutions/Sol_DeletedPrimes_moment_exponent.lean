-- Prove2me | solution 1 for DeletedPrimes.moment_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:08:29.917957+00:00
-- url     : https://prove2.me/submissions/019c479a-924b-4320-b2bc-ada6c305c98c

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α b : ℝ} : α - 1 - 2 * b < -1 ↔ α / 2 < b := by
  constructor <;> intro h <;> linarith
end DeletedPrimes
