-- Prove2me | solution 1 for BookProof.ChapterCoherentPositionSpace.packetBorn_eq_scoreSoftmax
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:32:31.915781+00:00
-- url     : https://prove2.me/submissions/1ec0c61f-94de-4f86-aebf-a2d01edbaf04

-- Generated from ChapterCoherentPositionSpace.lean — solution of BookProof.ChapterCoherentPositionSpace.packetBorn_eq_scoreSoftmax
import Mathlib
import Definitions.Def_ChapterCoherentPositionSpace
import Theorems.Thm_BookProof_ChapterCoherentPositionSpace_gaussianPacket_inner
open BookProof.ChapterCoherentPositionSpace



open scoped BigOperators
open MeasureTheory

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxSharpness

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (q : ℝ) (k : Fin m → ℝ) (j : Fin m) :
    packetBorn q k j = scoreSoftmax (1 / 2) (fun l => -(q - k l) ^ 2) j := by

  have hpt : ∀ l : Fin m,
      (∫ x : ℝ, gaussianPacket q x * gaussianPacket (k l) x) ^ 2
        = Real.exp (1 / 2 * -(q - k l) ^ 2) := by
    intro l
    rw [gaussianPacket_inner, ← Real.exp_nat_mul]
    ring_nf
  rw [packetBorn, scoreSoftmax, hpt j, Finset.sum_congr rfl fun l _ => hpt l]
