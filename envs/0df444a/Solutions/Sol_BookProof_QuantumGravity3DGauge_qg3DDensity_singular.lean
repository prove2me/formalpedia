-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qg3DDensity_singular
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T06:33:26.954081+00:00
-- url     : https://prove2.me/submissions/4cadfc0e-748d-4b93-bdea-18d9209d1e9f

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge
open Filter Topology

theorem solution : Tendsto (fun e : ℝ => (1 : ℝ) / e) (𝓝[>] (0 : ℝ)) atTop := by
  simpa [div_eq_inv_mul, one_mul] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
