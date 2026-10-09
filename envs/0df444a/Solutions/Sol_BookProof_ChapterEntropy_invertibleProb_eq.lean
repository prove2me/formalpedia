-- Prove2me | solution 1 for BookProof.ChapterEntropy.invertibleProb_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:39:39.298386+00:00
-- url     : https://prove2.me/submissions/244417b2-6243-49d8-8ee6-e75185a41ac0

-- Generated from ChapterEntropy.lean — solution of BookProof.ChapterEntropy.invertibleProb_eq
import Mathlib
import Definitions.Def_ChapterEntropy
import Theorems.Thm_BookProof_ChapterEntropy_card_bijections
open BookProof.ChapterEntropy




open Filter Asymptotics
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    invertibleProb n = (Nat.factorial n : ℝ) / (n ^ n : ℝ) := by

  simp [invertibleProb, card_bijections]
