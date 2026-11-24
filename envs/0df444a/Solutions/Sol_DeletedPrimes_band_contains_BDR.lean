-- Prove2me | solution 1 for DeletedPrimes.band_contains_BDR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:21:09.510832+00:00
-- url     : https://prove2.me/submissions/84b7b7c7-1227-417f-a5de-c0e4f20708ed

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) : α / 2 < 2 * α / (α + 2) := by
  rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
  nlinarith
end DeletedPrimes
