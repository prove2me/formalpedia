-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.confV_stone_flow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T22:14:54.220421+00:00
-- url     : https://prove2.me/submissions/b959bc44-9af0-49c3-b7c0-ca88e005eb5f

-- Generated from ChapterHermiteQuadraticEsa.lean — solution of BookProof.HermiteQuadraticEsa.confV_stone_flow
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
import Theorems.Thm_BookProof_HermiteQuadraticEsa_continuous_confW
import Theorems.Thm_BookProof_HermiteQuadraticEsa_expBounded_confW
import Theorems.Thm_BookProof_HermiteQuadraticEsa_confV_essentiallySelfAdjoint
import Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_symmetricOn
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
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
    ∃ (T : UnboundedSelfAdjoint (L2d 1)) (U : ℝ → (L2d 1 →L[ℂ] L2d 1)),
      IsSelfAdjointExtension
        (hamCore (confW M alpha) (continuous_confW M alpha) (expBounded_confW M alpha)) T.op
        ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ polyGaussCore_dense (hamCore_symmetricOn _ _ _)
      (confV_essentiallySelfAdjoint M alpha h0 h2)
