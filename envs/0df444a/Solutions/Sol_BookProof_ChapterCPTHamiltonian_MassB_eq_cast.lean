-- Prove2me | solution 1 for BookProof.ChapterCPTHamiltonian.MassB_eq_cast
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:54:32.592934+00:00
-- url     : https://prove2.me/submissions/1b0365c8-60b1-4054-8fda-27091ebd3524

-- Generated from ChapterCPTHamiltonian.lean — solution of BookProof.ChapterCPTHamiltonian.MassB_eq_cast
import Mathlib
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution :
    MassB = (Int.castRingHom ℂ).mapMatrix MassBZ := by

  rw [MassB, dgamma, dgamma5, MassBZ, map_neg, map_mul, mgamma, mgamma5]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_mul_neg, Complex.I_mul_I]
  simp
