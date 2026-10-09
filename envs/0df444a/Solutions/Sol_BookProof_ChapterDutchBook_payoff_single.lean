-- Prove2me | solution 1 for BookProof.ChapterDutchBook.payoff_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:25:08.435995+00:00
-- url     : https://prove2.me/submissions/015b1c32-76ac-4613-bc12-e0d9079e3a33

-- Generated from ChapterDutchBook.lean — solution of BookProof.ChapterDutchBook.payoff_single
import Mathlib
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterDutchBook



open scoped BigOperators
open Finset


variable {Ω : Type*} [DecidableEq Ω]

variable {Ω : Type*} [DecidableEq Ω]

set_option maxHeartbeats 1000000 in
theorem solution (Pr : Finset Ω → ℝ) (A₀ : Finset Ω) (s₀ : ℝ) (ω : Ω) :
    payoff Pr ![A₀] ![s₀] ω = s₀ * (betIndicator A₀ ω - Pr A₀) := by

  simp [payoff]
