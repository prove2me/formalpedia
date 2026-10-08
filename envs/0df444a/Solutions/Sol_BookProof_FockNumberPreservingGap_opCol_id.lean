-- Prove2me | solution 1 for BookProof.FockNumberPreservingGap.opCol_id
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:29:38.861344+00:00
-- url     : https://prove2.me/submissions/56ef3263-0216-41dd-b373-1d063e6822ab

-- Generated from ChapterFockNumberPreservingGap.lean — solution of BookProof.FockNumberPreservingGap.opCol_id
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Theorems.Thm_BookProof_FockSecondQuantization_opCol_apply
open BookProof.FockNumberPreservingGap



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (b : HilbertBasis ℕ ℂ F) (k j : ℕ) :
    opCol b (LinearMap.id) k j = if j = k then (1 : ℂ) else 0 := by

  rw [opCol_apply]
  simpa using orthonormal_iff_ite.mp b.orthonormal j k
