-- Prove2me | solution 1 for DeletedPrimes.pole_mem_halfplane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:20:40.984635+00:00
-- url     : https://prove2.me/submissions/6297f305-a7fa-4198-bba3-7e22c04b16e1

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α : ℝ} (hα0 : 0 < α) : α / 2 < α := by linarith
end DeletedPrimes
