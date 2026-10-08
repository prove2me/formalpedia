-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.confV_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T22:14:11.123758+00:00
-- url     : https://prove2.me/submissions/28d2a1b0-f216-429b-b1ad-a16ed719ea6b

-- Generated from ChapterHermiteQuadraticEsa.lean — solution of BookProof.HermiteQuadraticEsa.confV_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
import Theorems.Thm_BookProof_HermiteQuadraticEsa_quadraticGrowth_essentiallySelfAdjoint
import Theorems.Thm_BookProof_HermiteQuadraticEsa_continuous_confW
import Theorems.Thm_BookProof_HermiteQuadraticEsa_abs_confW_sub_harmW_le
import Theorems.Thm_BookProof_HermiteQuadraticEsa_expBounded_confW
open BookProof.HermiteQuadraticEsa




open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (h0 : 0 < alpha) (h2 : alpha < 1 / 2) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 1))
      (hamCore (confW M alpha) (continuous_confW M alpha) (expBounded_confW M alpha)) := by

  refine quadraticGrowth_essentiallySelfAdjoint (A := |alpha - 1 / 4|) (Ccoef := M ^ 2 / 2)
    (B := 0) _ _ (abs_nonneg _) ?_ le_rfl (abs_confW_sub_harmW_le M alpha)
  have habs : |alpha - 1 / 4| < 1 / 4 := by
    rw [abs_lt]
    constructor <;> linarith
  linarith
