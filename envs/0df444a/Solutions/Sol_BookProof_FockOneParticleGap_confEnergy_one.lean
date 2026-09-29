-- Prove2me | solution 1 for BookProof.FockOneParticleGap.confEnergy_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T21:47:58.417218+00:00
-- url     : https://prove2.me/submissions/15a2a9ed-272e-4e52-9a88-74646c7924de

import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology
noncomputable section

theorem solution (β : Conf) : confEnergy (fun _ => 1) β = (confNumber β : ℝ) := by
  simp [confEnergy, confNumber]
