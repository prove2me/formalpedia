-- Prove2me | solution 1 for BookProof.QuantumGravityDensitized.qgMetric_det
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:04:42.478872+00:00
-- url     : https://prove2.me/submissions/377c0a8f-d357-4f8e-9c48-88aa2ddd2849

-- Generated from ChapterQuantumGravityDensitized.lean — solution of BookProof.QuantumGravityDensitized.qgMetric_det
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
open BookProof.QuantumGravityDensitized




open Filter Topology BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    (qgMetric n).det = ∏ i, (if i = Fin.last n then -(1 / 24) else 1 / 16 : ℝ) := Matrix.det_diagonal
