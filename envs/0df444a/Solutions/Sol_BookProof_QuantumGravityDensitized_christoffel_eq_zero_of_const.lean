-- Prove2me | solution 1 for BookProof.QuantumGravityDensitized.christoffel_eq_zero_of_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:00:51.326199+00:00
-- url     : https://prove2.me/submissions/512dd56c-8585-4bd3-83cd-4fd11d3139c7

-- Generated from ChapterQuantumGravityDensitized.lean — solution of BookProof.QuantumGravityDensitized.christoffel_eq_zero_of_const
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
open BookProof.QuantumGravityDensitized




open Filter Topology BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (g0 : Matrix (Fin m) (Fin m) ℝ)
    (ginv : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (q : EuclideanSpace ℝ (Fin m)) (k i j : Fin m) :
    christoffel (fun _ => g0) ginv q k i j = 0 := by

  simp [christoffel, metricDeriv]
