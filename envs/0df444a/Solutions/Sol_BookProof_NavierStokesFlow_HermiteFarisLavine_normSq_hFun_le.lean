-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.normSq_hFun_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:48.075967+00:00
-- url     : https://prove2.me/submissions/cf923034-905b-47df-aa9c-32be5e83845b

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.normSq_hFun_le
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : 0 ≤ κ) (X : ℕ → ℂ) (m : ℕ) :
    ‖hFun κ X m‖ ^ 2
      ≤ 2 * shift2 (fun n => (ampSeq κ X n) ^ 2) m + 2 * (ampSeq κ X (m + 2)) ^ 2 := by

  have h1 := norm_hFun_le hκ X m
  have h2 : 0 ≤ shift2 (ampSeq κ X) m := shift2_nonneg _ (ampSeq_nonneg hκ _) m
  have h3 : 0 ≤ ampSeq κ X (m + 2) := ampSeq_nonneg hκ _ _
  have h4 := mul_self_le_mul_self (norm_nonneg (hFun κ X m)) h1
  rw [shift2_sq]
  nlinarith [h4, sq_nonneg (shift2 (ampSeq κ X) m - ampSeq κ X (m + 2))]
