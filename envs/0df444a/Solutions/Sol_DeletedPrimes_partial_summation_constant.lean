-- Prove2me | solution 1 for DeletedPrimes.partial_summation_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:19:33.844225+00:00
-- url     : https://prove2.me/submissions/140cf20a-6c0d-4259-9a54-5bc19395fafb

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {a β Y : ℝ} (hβ : β ≠ 1) :
    a * Y + a * β * (Y - 1) / (1 - β) = a * Y / (1 - β) + a * β / (β - 1) := by
  have h1 : (1 : ℝ) - β ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  have h2 : β - 1 ≠ 0 := sub_ne_zero.mpr hβ
  field_simp
  ring
end DeletedPrimes
