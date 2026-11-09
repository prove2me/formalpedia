-- Prove2me | solution 1 for BookProof.QuantumGravityDensitized.densTetrad_recover
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:01:59.527376+00:00
-- url     : https://prove2.me/submissions/ea3971eb-cef8-43cc-8829-c5d6e92fdb7c

-- Generated from ChapterQuantumGravityDensitized.lean — solution of BookProof.QuantumGravityDensitized.densTetrad_recover
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
open BookProof.QuantumGravityDensitized




open Filter Topology BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution {E : Matrix (Fin 3) (Fin 3) ℝ} (h : 0 < E.det) :
    (Real.sqrt E.det)⁻¹ • densTetrad E = E := by

  rw [densTetrad, smul_smul, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr h)), one_smul]
