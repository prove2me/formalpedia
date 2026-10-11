-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.commForm_ne_zero_of_pos
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:24.198143+00:00
-- url     : https://prove2.me/submissions/f6e6f006-b297-4639-8c5e-74c26188d316
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.commForm_ne_zero_of_pos
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_commForm_testState
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : 0 < κ) :
    commForm (nsH κ (le_of_lt hκ)) (diagMax (oscSymbol κ)) (testState κ) ≠ 0 := by

  rw [commForm_testState (le_of_lt hκ)]
  have hamp : 0 < amp κ 0 := by
    have : (0 : ℝ) < Real.sqrt ((0 + 1) * (0 + 2)) := by
      rw [Real.sqrt_pos]; norm_num
    simp only [amp]
    push_cast
    positivity
  positivity
