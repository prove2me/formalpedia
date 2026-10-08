-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.sectorQuad_stone_flow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T22:15:27.052761+00:00
-- url     : https://prove2.me/submissions/d2382190-f7a1-425b-9b9b-864d84aaf18c

-- Generated from ChapterHermiteQuadraticEsa.lean — solution of BookProof.HermiteQuadraticEsa.sectorQuad_stone_flow
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
import Theorems.Thm_BookProof_HermiteQuadraticEsa_continuous_sectorQuadW
import Theorems.Thm_BookProof_HermiteQuadraticEsa_expBounded_sectorQuadW
import Theorems.Thm_BookProof_HermiteQuadraticEsa_sectorQuad_essentiallySelfAdjoint
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
theorem solution (M alpha mu : ℝ) (ha0 : 0 < alpha) (ha2 : alpha < 1 / 2)
    (hm0 : 0 < mu) (hm2 : mu < 1 / 2) :
    ∃ (T : UnboundedSelfAdjoint (L2d 2)) (U : ℝ → (L2d 2 →L[ℂ] L2d 2)),
      IsSelfAdjointExtension
        (hamCore (sectorQuadW M alpha mu) (continuous_sectorQuadW M alpha mu)
          (expBounded_sectorQuadW M alpha mu)) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ polyGaussCore_dense (hamCore_symmetricOn _ _ _)
      (sectorQuad_essentiallySelfAdjoint M alpha mu ha0 ha2 hm0 hm2)
