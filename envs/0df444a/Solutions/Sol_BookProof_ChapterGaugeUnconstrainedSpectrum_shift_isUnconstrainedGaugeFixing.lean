-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.shift_isUnconstrainedGaugeFixing
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:40:18.189627+00:00
-- url     : https://prove2.me/submissions/470d30a8-1c01-460e-a6a2-2b49ecf93bba

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — solution of BookProof.ChapterGaugeUnconstrainedSpectrum.shift_isUnconstrainedGaugeFixing
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_isUnconstrained_of_movesEveryPoint
import Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_shiftPerm_movesEveryPoint
open BookProof.ChapterGaugeUnconstrainedSpectrum




variable {X : Type*}

variable {X : Type*}
variable {G : Type*} [Group G]

set_option maxHeartbeats 1000000 in
theorem solution :
    IsUnconstrainedGaugeFixing (fun m : Multiplicative ℤ => permOp (shiftPerm m)) := isUnconstrained_of_movesEveryPoint shiftPerm_movesEveryPoint
