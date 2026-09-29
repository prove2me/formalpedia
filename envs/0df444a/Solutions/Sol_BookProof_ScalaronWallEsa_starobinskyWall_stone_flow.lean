-- Prove2me | solution 1 for BookProof.ScalaronWallEsa.starobinskyWall_stone_flow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:12:24.966487+00:00
-- url     : https://prove2.me/submissions/962e33c8-bd27-4b6d-8e46-53fe2e6cfdc2

import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterWeakSecondDerivative
-- Generated from ChapterScalaronWallEsa.lean — solution of BookProof.ScalaronWallEsa.starobinskyWall_stone_flow
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
import Theorems.Thm_BookProof_ScalaronWallEsa_wallHam_symmetricOn
import Theorems.Thm_BookProof_ScalaronWallEsa_starobinskyWall_esa
import Theorems.Thm_BookProof_ScalaronEsa_contDiff_starobinskyV
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Theorems.Thm_BookProof_ScalaronEsa_ccDomain_dense
open BookProof.ScalaronWallEsa













open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {M alpha : ℝ} (halpha : 0 < alpha) :
    ∃ (T : UnboundedSelfAdjoint (Lp ℂ 2 (volume : Measure ℝ)))
      (U : ℝ → (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))),
      IsSelfAdjointExtension
          (wallHam (fun phi : ℝ => starobinskyV M alpha phi)
            (contDiff_starobinskyV M alpha)) T.op ∧
        IsStoneFlow T U := exists_stone_flow_of_esa _ ccDomain_dense (wallHam_symmetricOn _ _) (starobinskyWall_esa halpha)
