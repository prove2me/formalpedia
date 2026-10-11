-- Prove2me | solution 1 for BookProof.TempleSeparationNecessary.witness_other
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:53.986508+00:00
-- url     : https://prove2.me/submissions/5d1ec795-e118-4865-8757-3fdb1cd20dc6

-- Generated from ChapterTempleSeparationNecessary.lean — solution of BookProof.TempleSeparationNecessary.witness_other
import Mathlib
import Definitions.Def_ChapterTempleSeparationNecessary
import Theorems.Thm_BookProof_TempleSeparationNecessary_witness_apply
import Theorems.Thm_BookProof_TempleSeparationNecessary_inner_trial_other
import Definitions.Def_ChapterRitzCertificate
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.TempleSeparationNecessary



noncomputable section


open BookProof.RitzCertificate

set_option maxHeartbeats 1000000 in
theorem solution (M : ℝ) : witness M trial other = ((-M : ℝ) : ℂ) • other := by

  rw [witness_apply, inner_trial_other, zero_smul, sub_zero]
