-- Prove2me | solution 1 for BookProof.SirkFinitePrecision.CertInterval.abs_polyEval_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T17:12:47.055919+00:00
-- url     : https://prove2.me/submissions/4b9189c9-a0c8-4ca1-b9ed-5188db851ec5

-- Generated from ChapterSirkFinitePrecision.lean — solution of BookProof.SirkFinitePrecision.CertInterval.abs_polyEval_le_of_mem
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
import Theorems.Thm_BookProof_SirkFinitePrecision_CertInterval_mem_evalHorner
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval







noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (cs : List ℝ) (I : CertInterval) {x : ℝ} (hx : I.Mem x) :
    |polyEval cs x| ≤ max |(evalHorner cs I).lo| |(evalHorner cs I).hi| := by

  have h := mem_evalHorner cs I x hx
  rw [abs_le]
  constructor
  · have h1 : -|(evalHorner cs I).lo| ≤ (evalHorner cs I).lo := neg_abs_le _
    have h2 : -max |(evalHorner cs I).lo| |(evalHorner cs I).hi| ≤ -|(evalHorner cs I).lo| :=
      neg_le_neg (le_max_left _ _)
    linarith [h.1]
  · have h1 : (evalHorner cs I).hi ≤ |(evalHorner cs I).hi| := le_abs_self _
    have h2 : |(evalHorner cs I).hi| ≤ max |(evalHorner cs I).lo| |(evalHorner cs I).hi| :=
      le_max_right _ _
    linarith [h.2]
