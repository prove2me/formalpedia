-- Prove2me | solution 1 for BookProof.TempleSeparationNecessary.resid_witness
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:10:57.609753+00:00
-- url     : https://prove2.me/submissions/a691a9ec-01b9-4788-82c8-b8709f6f1063

-- Generated from ChapterTempleSeparationNecessary.lean — solution of BookProof.TempleSeparationNecessary.resid_witness
import Mathlib
import Definitions.Def_ChapterTempleSeparationNecessary
import Theorems.Thm_BookProof_TempleSeparationNecessary_witness_trial
import Theorems.Thm_BookProof_TempleSeparationNecessary_rayleigh_witness
import Definitions.Def_ChapterNavierStokesFarisLavineLift
import Definitions.Def_ChapterRitzCertificate
open BookProof.TempleSeparationNecessary



noncomputable section


open BookProof.RitzCertificate

set_option maxHeartbeats 1000000 in
theorem solution (M : ℝ) : resid (witness M trial) trial = 0 := by

  rw [resid, rayleigh_witness, witness_trial]
  norm_num
