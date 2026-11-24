-- Prove2me | solution 1 for DeletedPrimes.cross_terms_cancel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:19:30.320645+00:00
-- url     : https://prove2.me/submissions/0a878bd3-4b3b-459f-b9f4-1b821c010c6f

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {a β : ℝ} (hβ : β ≠ 1) : a / (1 - β) - a * β / (1 - β) - a = 0 := by
  have h : (1 : ℝ) - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  field_simp
  ring
end DeletedPrimes
