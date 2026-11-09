-- Prove2me | solution 1 for BookProof.QuantumGravityDensitized.qgSymbol_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:04:46.855653+00:00
-- url     : https://prove2.me/submissions/b3d6e74f-a077-47e4-9b91-329e8dfc670b

-- Generated from ChapterQuantumGravityDensitized.lean — solution of BookProof.QuantumGravityDensitized.qgSymbol_homogeneous
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
open BookProof.QuantumGravityDensitized




open Filter Topology BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (c : ℝ) (xi : Fin n → ℝ) (xiY : ℝ) :
    qgSymbol (fun a => c * xi a) (c * xiY) = c ^ 2 * qgSymbol xi xiY := by

  simp only [qgSymbol, mul_pow, ← Finset.mul_sum]
  ring
