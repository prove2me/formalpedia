-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossB
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:44.460608+00:00
-- url     : https://prove2.me/submissions/56e46974-1b6f-4244-929b-07f493aab8ee

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.summable_crossB
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_norm_crossB
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : 0 ≤ κ) {X Y : ℕ → ℂ}
    (hX : Summable fun n => (ampSeq κ X n) ^ 2) (hY : Summable fun n => ‖Y n‖ ^ 2) :
    Summable (crossB κ X Y) := by

  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((((summable_nat_add_iff 2).mpr hX).add hY).mul_left (1 / 2)))
  rw [norm_crossB hκ]
  have hmono : amp κ n * ‖X (n + 2)‖ ≤ ampSeq κ X (n + 2) :=
    mul_le_mul_of_nonneg_right (amp_le_amp_add_two hκ n) (norm_nonneg _)
  have h0 : 0 ≤ ‖Y n‖ := norm_nonneg _
  nlinarith [sq_nonneg (ampSeq κ X (n + 2) - ‖Y n‖), ampSeq_nonneg hκ X (n + 2),
    mul_le_mul_of_nonneg_right hmono h0]
