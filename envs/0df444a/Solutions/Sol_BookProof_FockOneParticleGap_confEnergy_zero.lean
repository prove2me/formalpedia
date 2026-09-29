-- Prove2me | solution 1 for BookProof.FockOneParticleGap.confEnergy_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T21:13:58.991792+00:00
-- url     : https://prove2.me/submissions/2d04ddea-4758-4911-a128-e68c3e3a9bd9

import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem solution (e : ℕ → ℝ) : confEnergy e (0 : Conf) = 0 := by
  simp [confEnergy]
