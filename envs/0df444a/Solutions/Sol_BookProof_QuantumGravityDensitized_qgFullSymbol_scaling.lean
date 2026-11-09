-- Prove2me | solution 1 for BookProof.QuantumGravityDensitized.qgFullSymbol_scaling
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:11:42.401491+00:00
-- url     : https://prove2.me/submissions/35aef35d-d7e4-4e2f-a098-700fe86f25ba

-- Generated from ChapterQuantumGravityDensitized.lean — solution of BookProof.QuantumGravityDensitized.qgFullSymbol_scaling
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Theorems.Thm_BookProof_QuantumGravityDensitized_qgSymbol_homogeneous
open BookProof.QuantumGravityDensitized




open Filter Topology BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (c : ℝ) (xi : Fin n → ℝ) (xiY : ℝ)
    (b : Fin n → ℝ) (bY : ℝ) (V : ℝ) :
    qgFullSymbol (fun a => c * xi a) (c * xiY) b bY V
      = c ^ 2 * qgSymbol xi xiY + c * ((∑ a, b a * xi a) + bY * xiY) - V := by

  simp only [qgFullSymbol, qgSymbol_homogeneous]
  have hsum : ∑ a, b a * (c * xi a) = c * ∑ a, b a * xi a := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsum]
  ring
