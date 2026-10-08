-- Prove2me | solution 1 for BookProof.FockNumberPreservingGap.dGamma_vac
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:25:19.05217+00:00
-- url     : https://prove2.me/submissions/8a1a14a4-a050-4bbb-95a9-7cef9c29dec9

-- Generated from ChapterFockNumberPreservingGap.lean — solution of BookProof.FockNumberPreservingGap.dGamma_vac
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Theorems.Thm_BookProof_FockSecondQuantization_annA_single
import Theorems.Thm_BookProof_FockSecondQuantization_dGamma_single
open BookProof.FockNumberPreservingGap



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (col : ℕ → (ℕ →₀ ℂ)) : dGamma col vac = 0 := by

  simp [vac, dGamma_single]
