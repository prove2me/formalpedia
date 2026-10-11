-- Prove2me | solution 1 for BookProof.ChapterSphericalBessel.sbessel_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:30.670443+00:00
-- url     : https://prove2.me/submissions/b6463ea0-de30-40ce-9ea2-388902c4240b

-- Generated from ChapterSphericalBessel.lean — solution of BookProof.ChapterSphericalBessel.sbessel_zero
import Mathlib
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel




open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution : sbessel 0 = sj0 := by

  funext r; simp [sbessel, sbesselBase, sj0]
