-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.summable_ampOcc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:18.654074+00:00
-- url     : https://prove2.me/submissions/3892581c-3549-4093-9361-6a978d6f5a36

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.summable_ampOcc
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_amp_le_symbol
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_hasSum_quadForm
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    Summable (fun n => amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2) := by

  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (amp_nonneg hκ n) (sq_nonneg _))
    (fun n => ?_) ((diagMax_hasSum_quadForm (oscSymbol κ) x).summable.mul_left (1 / 4 + κ / 2))
  nlinarith [amp_le_symbol hκ n, sq_nonneg ‖((x : L2I ℕ) : ℕ → ℂ) n‖]
