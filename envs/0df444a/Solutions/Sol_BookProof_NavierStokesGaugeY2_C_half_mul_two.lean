-- Prove2me | solution 1 for BookProof.NavierStokesGaugeY2.C_half_mul_two
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:20.515987+00:00
-- url     : https://prove2.me/submissions/e498da4b-e2fe-4318-b190-468cbaa21372

-- Generated from ChapterNavierStokesGaugeY2.lean — solution of BookProof.NavierStokesGaugeY2.C_half_mul_two
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY2




open MvPolynomial BookProof.NavierStokesGaugeY

set_option maxHeartbeats 1000000 in
theorem solution : (C (1 / 2 : ℂ) : NSAlg) * 2 = 1 := by

  rw [(map_ofNat C 2).symm, ← C_mul]
  norm_num
