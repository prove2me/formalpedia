-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.trial_cubic_quartic_bounded_below
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T11:55:19.078126+00:00
-- url     : https://prove2.me/submissions/a68e4e71-bef2-45c9-a234-b857a577e4bf

-- Generated from ChapterFockCubicUnbounded.lean — solution of BookProof.FockCubicUnbounded.trial_cubic_quartic_bounded_below
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_norm_sq
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_numberQuad
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_cubic_form
import Theorems.Thm_BookProof_FockCubicUnbounded_trial_quartic_form
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
theorem solution (k n : ℕ) (hn : 1 ≤ n) (lam c : ℝ) :
    -(lam ^ 4 / 4 + 2 * lam ^ 2) * ‖toLp (trial k n c)‖ ^ 2
      ≤ numberQuad (trial k n c)
        + lam * (inner ℂ (toLp (trial k n c)) (toLp (cubeA k (trial k n c))) : ℂ).re
        + (inner ℂ (toLp (trial k n c)) (toLp (quartA k (trial k n c))) : ℂ).re := by

  rw [trial_numberQuad, trial_cubic_form k n hn c, trial_quartic_form, trial_norm_sq]
  set t := Real.sqrt ((n : ℝ) + 2) with htdef
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = (n : ℝ) + 2 := Real.sq_sqrt (by positivity)
  set S := Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3)) with hSdef
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS : S ≤ t ^ 3 := by
    have hcube : (0 : ℝ) ≤ t ^ 3 := by positivity
    have hle : ((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) ≤ (t ^ 3) ^ 2 := by
      have : (t ^ 3) ^ 2 = ((n : ℝ) + 2) ^ 3 := by
        rw [show (t ^ 3) ^ 2 = (t ^ 2) ^ 3 from by ring, ht2]
      rw [this]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq hcube] at this
  -- the cubic term is dominated by the quartic term up to `lam²(n+2)`
  have key1 : -(c ^ 2 * ((n : ℝ) + 2) ^ 2 + lam ^ 2 * ((n : ℝ) + 2)) ≤ lam * (2 * c * S) := by
    rcases le_or_gt 0 (lam * c) with hsign | hsign
    · have h1 : 0 ≤ lam * (2 * c * S) := by nlinarith
      nlinarith [sq_nonneg c, sq_nonneg lam, Nat.cast_nonneg (α := ℝ) n]
    · have h2 : lam * (2 * c * t ^ 3) ≤ lam * (2 * c * S) := by nlinarith
      have h3 : 0 ≤ t ^ 2 * (c * t + lam) ^ 2 := by positivity
      have ht4 : t ^ 4 = ((n : ℝ) + 2) ^ 2 := by
        rw [show t ^ 4 = (t ^ 2) ^ 2 from by ring, ht2]
      have hexp : t ^ 2 * (c * t + lam) ^ 2
          = c ^ 2 * ((n : ℝ) + 2) ^ 2 + lam * (2 * c * t ^ 3) + lam ^ 2 * ((n : ℝ) + 2) := by
        rw [show t ^ 2 * (c * t + lam) ^ 2
          = c ^ 2 * t ^ 4 + lam * (2 * c * t ^ 3) + lam ^ 2 * t ^ 2 from by ring, ht4, ht2]
      linarith [h2, h3, hexp.symm.le, hexp.le]
  -- the quadratic-in-`n` free and quartic terms absorb the remainder
  have key2 : -(lam ^ 4 / 4 + 2 * lam ^ 2)
      ≤ (n : ℝ) + (n : ℝ) * ((n : ℝ) - 1) - lam ^ 2 * ((n : ℝ) + 2) := by
    nlinarith [sq_nonneg ((n : ℝ) - lam ^ 2 / 2)]
  have key3 : 0 ≤ c ^ 2 * ((n : ℝ) + 3) + ((n : ℝ) + 3) * ((n : ℝ) + 2) * c ^ 2
      - c ^ 2 * ((n : ℝ) + 2) ^ 2 := by
    have : c ^ 2 * ((n : ℝ) + 3) + ((n : ℝ) + 3) * ((n : ℝ) + 2) * c ^ 2
        - c ^ 2 * ((n : ℝ) + 2) ^ 2 = c ^ 2 * (2 * (n : ℝ) + 5) := by ring
    rw [this]; positivity
  have hMnn : 0 ≤ lam ^ 4 / 4 + 2 * lam ^ 2 := by positivity
  nlinarith [key1, key2, key3, hMnn, sq_nonneg c]
