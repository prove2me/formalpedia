-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.trial_vacuum_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:12:20.827322+00:00
-- url     : https://prove2.me/submissions/832332d5-4c8b-4d51-b978-ce9d01e95943

-- Generated from ChapterFockCubicUnbounded.lean — solution of BookProof.FockCubicUnbounded.trial_vacuum_orthogonal
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_at_other
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterTempleSeparationNecessary
open BookProof.FockCubicUnbounded



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockSecondQuantization
open BookProof.TempleSeparationNecessary

set_option maxHeartbeats 1000000 in
theorem solution {k n : ℕ} (hn : n ≠ 0) (c : ℝ) : trial k n c 0 = 0 := by

  have h0 : (0 : Conf) = confAt k 0 := by simp [confAt]
  rw [h0]
  exact trial_at_other (by omega) (by omega)
