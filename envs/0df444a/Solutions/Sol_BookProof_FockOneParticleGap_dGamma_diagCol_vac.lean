-- Prove2me | solution 1 for BookProof.FockOneParticleGap.dGamma_diagCol_vac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T21:45:16.213151+00:00
-- url     : https://prove2.me/submissions/0bc91fd5-77e6-4f26-a0ef-fceebf25c874

import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology
noncomputable section

theorem solution (e : ℕ → ℝ) : dGamma (diagCol e) vac = 0 := by
  simp [dGamma, diagCol, vac]
