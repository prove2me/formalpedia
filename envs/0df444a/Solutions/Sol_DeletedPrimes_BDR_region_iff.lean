-- Prove2me | solution 1 for DeletedPrimes.BDR_region_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:21:35.529285+00:00
-- url     : https://prove2.me/submissions/22d956a8-1e32-42e3-8bdf-1fdc17fd3312

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α : ℝ} (hα0 : 0 < α) : 2 * α / (α + 2) < 1 / 2 ↔ α < 2 / 3 := by
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  constructor <;> intro h <;> linarith
end DeletedPrimes
