-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.Ep_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:39:06.817894+00:00
-- url     : https://prove2.me/submissions/27429fbd-9640-46dd-b7c6-877845f90896

-- Generated from ChapterMajoranaFourier.lean — solution of BookProof.ChapterMajoranaFourier.Ep_ge
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterMajoranaFourier



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (m q : ℝ) (_hm : 0 ≤ m) : m ≤ Ep m q := by

  exact Real.le_sqrt_of_sq_le ( by nlinarith )
