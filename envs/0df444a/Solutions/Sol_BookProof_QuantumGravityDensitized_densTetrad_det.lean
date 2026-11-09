-- Prove2me | solution 1 for BookProof.QuantumGravityDensitized.densTetrad_det
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:01:40.991241+00:00
-- url     : https://prove2.me/submissions/fb7226c2-dfac-46b9-b409-3b534a535cca

-- Generated from ChapterQuantumGravityDensitized.lean — solution of BookProof.QuantumGravityDensitized.densTetrad_det
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
open BookProof.QuantumGravityDensitized




open Filter Topology BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution (E : Matrix (Fin 3) (Fin 3) ℝ) :
    (densTetrad E).det = Real.sqrt E.det ^ 3 * E.det := by

  simp [densTetrad]
