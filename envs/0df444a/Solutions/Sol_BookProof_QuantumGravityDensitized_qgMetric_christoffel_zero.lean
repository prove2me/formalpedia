-- Prove2me | solution 1 for BookProof.QuantumGravityDensitized.qgMetric_christoffel_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:09:01.569187+00:00
-- url     : https://prove2.me/submissions/86fa4f86-ddd4-46dc-b94f-18ad2e1d45c0

-- Generated from ChapterQuantumGravityDensitized.lean — solution of BookProof.QuantumGravityDensitized.qgMetric_christoffel_zero
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Theorems.Thm_BookProof_QuantumGravityDensitized_christoffel_eq_zero_of_const
open BookProof.QuantumGravityDensitized




open Filter Topology BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ}
    (ginv : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : EuclideanSpace ℝ (Fin (n + 1))) (k i j : Fin (n + 1)) :
    christoffel (fun _ => qgMetric n) ginv q k i j = 0 := christoffel_eq_zero_of_const _ ginv q k i j
