-- Prove2me | solution 1 for BookProof.ChapterRotaryPosition.coherentOverlapC_rotaryEncode
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:47.269265+00:00
-- url     : https://prove2.me/submissions/de1886a8-c7cd-4799-bfca-948e940a34b6

-- Generated from ChapterRotaryPosition.lean — solution of BookProof.ChapterRotaryPosition.coherentOverlapC_rotaryEncode
import Mathlib
import Definitions.Def_ChapterRotaryPosition
import Theorems.Thm_BookProof_ChapterRotaryPosition_norm_rotaryEncode
import Theorems.Thm_BookProof_ChapterRotaryPosition_inner_rotaryEncode
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterRotaryPosition



open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (omega : Fin n → ℝ) (a b : ℝ)
    (q k : EuclideanSpace ℂ (Fin n)) :
    coherentOverlapC (rotaryEncode omega a q) (rotaryEncode omega b k)
      = coherentOverlapC q (rotaryEncode omega (b - a) k) := by

  rw [coherentOverlapC, coherentOverlapC, norm_rotaryEncode, norm_rotaryEncode,
    norm_rotaryEncode, inner_rotaryEncode]
