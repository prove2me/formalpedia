-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.sectorHarmonicApprox_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T22:15:10.504564+00:00
-- url     : https://prove2.me/submissions/ae481a0a-f603-450f-a214-ab9cc795620b

-- Generated from ChapterHermiteQuadraticEsa.lean — solution of BookProof.HermiteQuadraticEsa.sectorHarmonicApprox_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
import Theorems.Thm_BookProof_HermiteQuadraticEsa_sectorQuad_essentiallySelfAdjoint
open BookProof.HermiteQuadraticEsa




open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (hM : M ≠ 0)
    (ha0 : 0 < alpha) (ha2 : alpha < 1 / 2) (hMa : M ^ 2 < 12 * alpha) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 2))
      (hamCore (sectorQuadW M alpha (M ^ 2 / (24 * alpha)))
        (continuous_sectorQuadW M alpha (M ^ 2 / (24 * alpha)))
        (expBounded_sectorQuadW M alpha (M ^ 2 / (24 * alpha)))) := by

  have hM2 : 0 < M ^ 2 := by positivity
  refine sectorQuad_essentiallySelfAdjoint M alpha _ ha0 ha2 (by positivity) ?_
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 24 * alpha)]
  linarith
