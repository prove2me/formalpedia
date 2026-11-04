-- Prove2me | solution 1 for BookProof.SirkSingleTime.singleTime_flow_tendsto_of_strongResAt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T02:08:01.051397+00:00
-- url     : https://prove2.me/submissions/cfb88e07-bdf7-4790-8f76-72a5ca47dddb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSirkSingleTimeShift.lean — solution of BookProof.SirkSingleTime.singleTime_flow_tendsto_of_strongResAt
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Theorems.Thm_BookProof_SirkSingleTime_strongResolventConvergence_of_strongResAt
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_trotterKato_tendsto
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.SirkSingleTime



open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}

set_option maxHeartbeats 1000000 in
theorem solution {l : ℝ} (hl : l ≠ 0)
    (h : StrongResAt T S l) (v : E) (t : ℝ) :
    Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := trotterKato_tendsto T S (strongResolventConvergence_of_strongResAt hl h) v t
