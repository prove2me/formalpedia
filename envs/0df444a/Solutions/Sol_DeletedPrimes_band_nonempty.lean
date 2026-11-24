-- Prove2me | solution 1 for DeletedPrimes.band_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:21:05.66424+00:00
-- url     : https://prove2.me/submissions/f9175d99-ba3c-47a6-a075-c5b4fa04238a

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α : ℝ} (hα1 : α < 1) : α / 2 < 1 / 2 := by linarith
end DeletedPrimes
