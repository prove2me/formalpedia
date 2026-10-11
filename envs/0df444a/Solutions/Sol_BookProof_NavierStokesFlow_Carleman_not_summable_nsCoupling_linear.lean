-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.not_summable_nsCoupling_linear
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:07.845127+00:00
-- url     : https://prove2.me/submissions/781a89ac-3ec1-4d54-87c8-57faf208207d

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.not_summable_nsCoupling_linear
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_norm_nsCoupling_linear
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution :
    ¬ Summable fun n : ℕ => 1 / ‖nsCoupling (fun m : ℕ => (m : ℝ) + 1) n‖ := by

  intro hs
  have hle : ∀ n : ℕ, 1 / (((n : ℝ) + 2)) ≤ 1 / ‖nsCoupling (fun m : ℕ => (m : ℝ) + 1) n‖ := by
    intro n
    rw [norm_nsCoupling_linear]
    have h1 : (0 : ℝ) < (n : ℝ) + 3 / 2 := by positivity
    have h2 : (n : ℝ) + 3 / 2 ≤ (n : ℝ) + 2 := by linarith
    exact one_div_le_one_div_of_le h1 h2
  have hsum : Summable fun n : ℕ => 1 / (((n : ℝ) + 2)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hs
  have hcast : (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) = fun n : ℕ => 1 / (((n : ℝ) + 2)) := by
    funext n; push_cast; ring
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 2).1 (by rw [hcast]; exact hsum))
