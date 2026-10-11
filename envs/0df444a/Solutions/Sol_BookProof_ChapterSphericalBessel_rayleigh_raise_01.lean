-- Prove2me | solution 1 for BookProof.ChapterSphericalBessel.rayleigh_raise_01
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:31.748984+00:00
-- url     : https://prove2.me/submissions/ef30065d-6dac-40c6-8ff6-6b7b88dc320f

-- Generated from ChapterSphericalBessel.lean — solution of BookProof.ChapterSphericalBessel.rayleigh_raise_01
import Mathlib
import Definitions.Def_ChapterSphericalBessel
import Theorems.Thm_BookProof_ChapterSphericalBessel_deriv_sbesselBase
open BookProof.ChapterSphericalBessel




open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution {r : ℝ} (hr : r ≠ 0) : sj1 r = -deriv sj0 r := by

  have hd : deriv sj0 r = Real.cos r / r - Real.sin r / r ^ 2 := deriv_sbesselBase hr
  rw [hd, sj1]; ring
