-- Prove2me | solution 1 for BookProof.FockFieldPerturbation.two_mul_sqrt_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:00:15.301285+00:00
-- url     : https://prove2.me/submissions/44d8916d-78b6-4dfb-a1b1-5d59bcb521a0

import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Mathlib
import Definitions.Def_ChapterFockFieldPerturbation
-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.two_mul_sqrt_le
open BookProof.FockFieldPerturbation


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability


theorem solution {c n N t : ℝ} (hN : 0 ≤ N) (ht : 0 < t) :
    2 * c * Real.sqrt N * n ≤ t * N + c ^ 2 / t * n ^ 2 := by
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN
  have key : 0 ≤ t * (t * N + c ^ 2 / t * n ^ 2 - 2 * c * Real.sqrt N * n) := by
    have : t * (t * N + c ^ 2 / t * n ^ 2 - 2 * c * Real.sqrt N * n)
        = (t * Real.sqrt N - c * n) ^ 2 := by
      field_simp
      nth_rewrite 1 [← hs]; ring
    rw [this]; positivity
  have := (mul_nonneg_iff_of_pos_left ht).mp key
  linarith

