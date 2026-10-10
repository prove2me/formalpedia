-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.amp_le_symbol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:38.475422+00:00
-- url     : https://prove2.me/submissions/0c4a1af7-f922-43a1-ba23-677d59efb3a7

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.amp_le_symbol
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : 0 ≤ κ) (n : ℕ) :
    amp κ n ≤ (1 / 4 + κ / 2) * oscSymbol κ n := by

  have h1 := amp_le_quarter hκ n
  have h2 : (1 : ℝ) ≤ oscSymbol κ n := oscSymbol_ge_one hκ n
  nlinarith
