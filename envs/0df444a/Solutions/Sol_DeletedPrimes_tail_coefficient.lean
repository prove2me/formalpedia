-- Prove2me | solution 1 for DeletedPrimes.tail_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:19:36.003984+00:00
-- url     : https://prove2.me/submissions/4479f078-6c75-46d8-9f41-b100a3fec27b

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {β : ℝ} (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) : 1 / (1 / β - 1) = β / (1 - β) := by
  have h : (1 : ℝ) - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ1)
  rw [show 1 / β - 1 = (1 - β) / β by field_simp, one_div_div]
end DeletedPrimes
