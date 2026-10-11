-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_commForm_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:20.996121+00:00
-- url     : https://prove2.me/submissions/760eec05-95a0-43b2-a80b-2b0b49cf6f45
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.nsH_commForm_bound
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_tsum_shift_le
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_hasSum_commForm
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_summable_ampOcc
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_tsum_ampOcc_le
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_abs_le_of_hasSum
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_quadForm_nonneg
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
    |commForm (nsH κ hκ) (diagMax (oscSymbol κ)) x|
      ≤ (2 * κ + 4 * κ ^ 2) * quadForm (diagMax (oscSymbol κ)) x := by

  have hus := summable_ampOcc hκ x
  have hutail : Summable (fun n => amp κ (n + 2) * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2) :=
    (summable_nat_add_iff 2).mpr hus
  have hbound : HasSum (fun n => 4 * κ * (amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2
      + amp κ (n + 2) * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2))
      (4 * κ * ((∑' n, amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2)
        + ∑' n, amp κ (n + 2) * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2)) :=
    (hus.hasSum.add hutail.hasSum).mul_left (4 * κ)
  have hptle : ∀ n, |8 * κ * (amp κ n * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
        * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re)|
      ≤ 4 * κ * (amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2
        + amp κ (n + 2) * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2) := by
    intro n
    have hamp : 0 ≤ amp κ n := amp_nonneg hκ n
    have hre : |((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
        * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re|
        ≤ ‖((x : L2I ℕ) : ℕ → ℂ) n‖ * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ := by
      refine le_trans (Complex.abs_re_le_norm _) ?_
      rw [norm_mul, RCLike.norm_conj]
    have habs : |8 * κ * (amp κ n * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
          * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re)|
        = 8 * κ * amp κ n * |((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
          * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re| := by
      rw [show (8 : ℝ) * κ * (amp κ n * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
          * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re)
          = (8 * κ * amp κ n) * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
            * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re from by ring, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 * κ * amp κ n)]
    have h1 : 8 * κ * amp κ n * |((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
          * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re|
        ≤ 8 * κ * amp κ n * (‖((x : L2I ℕ) : ℕ → ℂ) n‖ * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖) :=
      mul_le_mul_of_nonneg_left hre (by positivity)
    have hkey : 8 * κ * amp κ n * (‖((x : L2I ℕ) : ℕ → ℂ) n‖ * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖)
        ≤ 4 * κ * (amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2
          + amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2) := by
      have h2ab : 2 * (‖((x : L2I ℕ) : ℕ → ℂ) n‖ * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖)
          ≤ ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2 + ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2 := by
        nlinarith [sq_nonneg (‖((x : L2I ℕ) : ℕ → ℂ) n‖ - ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖)]
      have := mul_le_mul_of_nonneg_left h2ab
        (show (0 : ℝ) ≤ 4 * κ * amp κ n by positivity)
      linarith [this]
    have hmono : 4 * κ * (amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2)
        ≤ 4 * κ * (amp κ (n + 2) * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (amp_le_amp_add_two hκ n) (sq_nonneg _)) (by positivity)
    rw [habs]
    linarith
  have habs := abs_le_of_hasSum (hasSum_commForm hκ x) hbound hptle
  have htail : (∑' n, amp κ (n + 2) * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2)
      ≤ ∑' n, amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2 :=
    tsum_shift_le hus (fun n => mul_nonneg (amp_nonneg hκ n) (sq_nonneg _))
  have hU := tsum_ampOcc_le hκ x
  have hqf : 0 ≤ quadForm (diagMax (oscSymbol κ)) x :=
    diagMax_quadForm_nonneg _ (oscSymbol_nonneg hκ) x
  refine le_trans habs ?_
  nlinarith [hU, htail, hκ]
