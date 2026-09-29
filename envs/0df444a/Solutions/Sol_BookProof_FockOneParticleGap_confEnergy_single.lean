-- Prove2me | solution 1 for BookProof.FockOneParticleGap.confEnergy_single
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T21:48:01.756321+00:00
-- url     : https://prove2.me/submissions/842b9e02-17d0-48e4-858d-0bdc68a3ef7a

import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology
noncomputable section

theorem solution (e : ℕ → ℝ) (k : ℕ) :
    confEnergy e (Finsupp.single k 1) = e k := by
  simp [confEnergy]
