-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:26.501371+00:00
-- url     : https://prove2.me/submissions/d9393567-46ab-4a69-9a61-86158505ceff

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.nsSymbol_ge_one
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (d : ℕ) (p q : Fin d → ℕ → ℝ) (k : ℕ) : 1 ≤ nsSymbol d p q k := by

  have h1 : (0 : ℝ) ≤ ∑ i, p i k ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : (0 : ℝ) ≤ ∑ i, q i k ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [nsSymbol]
  linarith
