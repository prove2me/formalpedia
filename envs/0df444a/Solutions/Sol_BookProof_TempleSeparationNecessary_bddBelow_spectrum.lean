-- Prove2me | solution 1 for BookProof.TempleSeparationNecessary.bddBelow_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:00.47+00:00
-- url     : https://prove2.me/submissions/ccbb24c5-722b-4505-bee9-1b6a85802dce

-- Generated from ChapterTempleSeparationNecessary.lean — solution of BookProof.TempleSeparationNecessary.bddBelow_spectrum
import Mathlib
import Definitions.Def_ChapterTempleSeparationNecessary
import Definitions.Def_ChapterRitzCertificate
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.TempleSeparationNecessary



noncomputable section


open BookProof.RitzCertificate

set_option maxHeartbeats 1000000 in
theorem solution (A : E2 →L[ℂ] E2) : BddBelow (spectrum ℝ A) := by

  refine ⟨-‖A‖, fun t ht => ?_⟩
  have h := spectrum.norm_le_norm_of_mem ht
  have : |t| ≤ ‖A‖ := by simpa [Real.norm_eq_abs] using h
  cases abs_le.mp this with
  | intro h1 _ => exact h1
