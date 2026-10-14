-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampOcc_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:19.731588+00:00
-- url     : https://prove2.me/submissions/195ee7ce-ba59-421b-ba7a-c9f3da910a0d

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.tsum_ampOcc_le
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_amp_le_symbol
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_summable_ampOcc
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
    (∑' n, amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2)
      ≤ (1 / 4 + κ / 2) * quadForm (diagMax (oscSymbol κ)) x := by

  have hq := diagMax_hasSum_quadForm (oscSymbol κ) x
  refine le_trans (Summable.tsum_le_tsum (fun n => ?_) (summable_ampOcc hκ x)
    (hq.summable.mul_left (1 / 4 + κ / 2))) ?_
  · nlinarith [amp_le_symbol hκ n, sq_nonneg ‖((x : L2I ℕ) : ℕ → ℂ) n‖]
  · exact le_of_eq (hq.mul_left (1 / 4 + κ / 2)).tsum_eq
