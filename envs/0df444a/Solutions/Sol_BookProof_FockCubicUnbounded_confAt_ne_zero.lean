-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.confAt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T11:51:53.554197+00:00
-- url     : https://prove2.me/submissions/72885a43-48b1-4d75-9ca2-1938623e1fa0

-- Generated from ChapterFockCubicUnbounded.lean — solution of BookProof.FockCubicUnbounded.confAt_ne_zero
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Theorems.Thm_BookProof_FockCubicUnbounded_confAt_self
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockCubicUnbounded



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockSecondQuantization

set_option maxHeartbeats 1000000 in
theorem solution {k m : ℕ} (h : m ≠ 0) : confAt k m ≠ 0 := by

  intro hc
  have := congrArg (fun β : Conf => β k) hc
  simp only [confAt_self] at this
  exact h this
