-- Prove2me | solution 1 for BookProof.ChapterG3.free_remnant_moves_every_point
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T13:01:58.934383+00:00
-- url     : https://prove2.me/submissions/55422a95-2147-480a-bb8f-3500eb3a30a5

-- Generated from ChapterG3.lean — solution of BookProof.ChapterG3.free_remnant_moves_every_point
import Mathlib
import Definitions.Def_ChapterG3
open BookProof.ChapterG3



open MeasureTheory
open scoped ENNReal



variable {X : Type*}

variable {X : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {G Y : Type*} [Group G] [MulAction G Y]
    (hfree : ∀ (g : G) (y : Y), g • y = y → g = 1) {g : G} (hg : g ≠ 1) (y : Y) :
    g • y ≠ y := fun h => hg (hfree g y h)
