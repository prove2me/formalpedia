-- Prove2me | solution 1 for BookProof.ChapterDutchBook.payoff_triple
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:25:09.56241+00:00
-- url     : https://prove2.me/submissions/262f1f1f-dfed-4805-af47-7d201514708c

-- Generated from ChapterDutchBook.lean — solution of BookProof.ChapterDutchBook.payoff_triple
import Mathlib
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterDutchBook



open scoped BigOperators
open Finset


variable {Ω : Type*} [DecidableEq Ω]

variable {Ω : Type*} [DecidableEq Ω]

set_option maxHeartbeats 1000000 in
theorem solution (Pr : Finset Ω → ℝ) (A₀ A₁ A₂ : Finset Ω)
    (s₀ s₁ s₂ : ℝ) (ω : Ω) :
    payoff Pr ![A₀, A₁, A₂] ![s₀, s₁, s₂] ω =
      s₀ * (betIndicator A₀ ω - Pr A₀) + s₁ * (betIndicator A₁ ω - Pr A₁)
        + s₂ * (betIndicator A₂ ω - Pr A₂) := by

  simp [payoff, Fin.sum_univ_three]
