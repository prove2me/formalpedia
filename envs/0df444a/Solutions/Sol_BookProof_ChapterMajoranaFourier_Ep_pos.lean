-- Prove2me | solution 1 for BookProof.ChapterMajoranaFourier.Ep_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:39:02.705744+00:00
-- url     : https://prove2.me/submissions/e7a87547-42c6-4c1a-ad30-5c27aec25dae

-- Generated from ChapterMajoranaFourier.lean — solution of BookProof.ChapterMajoranaFourier.Ep_pos
import Mathlib
import Definitions.Def_ChapterMajoranaFourier
import Definitions.Def_ChapterA3
open BookProof.ChapterMajoranaFourier



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution (m q : ℝ) (hq : 0 < q) : 0 < Ep m q := by

  exact Real.sqrt_pos.mpr ( by positivity )
