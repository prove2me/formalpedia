-- Prove2me | solution 1 for BookProof.ChapterRotaryPosition.bornNumerC_rotaryEncode_shift
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:48.259299+00:00
-- url     : https://prove2.me/submissions/865cc118-ad4c-43af-bf5c-337c325aecab

-- Generated from ChapterRotaryPosition.lean — solution of BookProof.ChapterRotaryPosition.bornNumerC_rotaryEncode_shift
import Mathlib
import Definitions.Def_ChapterRotaryPosition
import Theorems.Thm_BookProof_ChapterRotaryPosition_coherentOverlapC_rotaryEncode
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterRotaryPosition



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (omega : Fin n → ℝ) (a b c : ℝ)
    (q k : EuclideanSpace ℂ (Fin n)) :
    bornNumerC (rotaryEncode omega (a + c) q) (rotaryEncode omega (b + c) k)
      = bornNumerC (rotaryEncode omega a q) (rotaryEncode omega b k) := by

  rw [bornNumerC, bornNumerC, coherentOverlapC_rotaryEncode, coherentOverlapC_rotaryEncode,
    show b + c - (a + c) = b - a from by ring]
