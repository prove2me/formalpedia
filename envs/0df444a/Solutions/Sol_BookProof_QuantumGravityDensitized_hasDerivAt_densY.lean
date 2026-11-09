-- Prove2me | solution 1 for BookProof.QuantumGravityDensitized.hasDerivAt_densY
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:03:33.74972+00:00
-- url     : https://prove2.me/submissions/3cd4eae5-77bd-4c6a-ab5f-86eac37bdb08

-- Generated from ChapterQuantumGravityDensitized.lean — solution of BookProof.QuantumGravityDensitized.hasDerivAt_densY
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
open BookProof.QuantumGravityDensitized




open Filter Topology BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution {e : ℝ} (he : e ≠ 0) :
    HasDerivAt densY (1 / (2 * Real.sqrt e)) e := Real.hasDerivAt_sqrt he
