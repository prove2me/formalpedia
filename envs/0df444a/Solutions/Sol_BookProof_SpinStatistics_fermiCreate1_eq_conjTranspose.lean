-- Prove2me | solution 1 for BookProof.SpinStatistics.fermiCreate1_eq_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:12.608452+00:00
-- url     : https://prove2.me/submissions/7f4f294e-1e86-4665-a20a-cddf8053f76a

-- Generated from ChapterSpinStatistics.lean — solution of BookProof.SpinStatistics.fermiCreate1_eq_conjTranspose
import Mathlib
import Definitions.Def_ChapterSpinStatistics
open BookProof.SpinStatistics




open Matrix

set_option maxHeartbeats 1000000 in
theorem solution : fermiCreate1 = fermiAnnih1ᴴ := rfl
