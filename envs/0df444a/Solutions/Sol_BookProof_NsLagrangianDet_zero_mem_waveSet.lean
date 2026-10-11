-- Prove2me | solution 1 for BookProof.NsLagrangianDet.zero_mem_waveSet
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:24.096911+00:00
-- url     : https://prove2.me/submissions/94b3407a-c420-4f26-9d4c-791784b75114

-- Generated from ChapterNsLagrangianDetConvolution.lean — solution of BookProof.NsLagrangianDet.zero_mem_waveSet
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet




open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

variable {K : Type*} [Fintype K]

set_option maxHeartbeats 1000000 in
theorem solution (kv : K → Fin 3 → ℝ) : (0 : Fin 3 → ℝ) ∈ waveSet kv := by

  classical
  refine Finset.mem_image.mpr ⟨fun _ => none, Finset.mem_univ _, ?_⟩
  simp [tupleWave, owv]
