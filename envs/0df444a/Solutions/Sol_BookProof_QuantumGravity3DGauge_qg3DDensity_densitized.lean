-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qg3DDensity_densitized
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T06:33:27.851401+00:00
-- url     : https://prove2.me/submissions/5a3bfc79-6e9d-4bec-b736-49b883b7e102

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge
open BookProof.QuantumGravityDensitized

theorem solution (e s p : ℝ) (he : 0 < e) :
    qg3DDensity e s p = 1 / 16 * (s / densY e) ^ 2 - 1 / 24 * (p / densY e) ^ 2 := by
  simp [qg3DDensity, densY, div_pow, Real.sq_sqrt he.le]
  ring
