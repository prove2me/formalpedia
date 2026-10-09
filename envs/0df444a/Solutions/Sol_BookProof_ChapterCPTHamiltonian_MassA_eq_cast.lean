-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.MassA_eq_cast
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:54:31.559508+00:00
-- url     : https://prove2.me/submissions/0d5a009c-e540-4734-bc9c-4e597f530f91

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.MassA_eq_cast
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution :
    MassA = (Int.castRingHom ℂ).mapMatrix MassAZ := by

  rw [MassA, dgamma, MassAZ, mgamma, smul_smul]
  simp
