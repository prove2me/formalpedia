-- Prove2me | solution 1 for BookProof.QuantumGravityDensitized.qgMetric_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:11:38.613658+00:00
-- url     : https://prove2.me/submissions/f712c989-e4da-4c1d-af26-bfba1360d780

-- Generated from ChapterQuantumGravityDensitized.lean — solution of BookProof.QuantumGravityDensitized.qgMetric_det_ne_zero
import Mathlib
import Definitions.Def_ChapterQuantumGravityDensitized
import Theorems.Thm_BookProof_QuantumGravityDensitized_qgMetric_det
open BookProof.QuantumGravityDensitized




open Filter Topology BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : (qgMetric n).det ≠ 0 := by

  rw [qgMetric_det]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  by_cases h : i = Fin.last n <;> simp [h]
