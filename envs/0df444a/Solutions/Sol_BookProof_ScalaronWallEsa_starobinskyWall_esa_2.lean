-- Prove2me | solution 2 for BookProof.ScalaronWallEsa.starobinskyWall_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:12:24.142205+00:00
-- url     : https://prove2.me/submissions/dabf7bc8-59d0-48d7-8db9-1c4d4a63b082

import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterWeakSecondDerivative
-- Generated from ChapterScalaronWallEsa.lean — solution of BookProof.ScalaronWallEsa.starobinskyWall_esa
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
import Theorems.Thm_BookProof_ScalaronWallEsa_wallHam_essentiallySelfAdjoint
import Theorems.Thm_BookProof_ScalaronEsa_contDiff_starobinskyV
import Theorems.Thm_BookProof_Starobinsky_starobinskyV_nonneg
open BookProof.ScalaronWallEsa













open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {M alpha : ℝ} (halpha : 0 < alpha) :
    EssentiallySelfAdjointOn (ccDomain ℝ)
      (wallHam (fun phi : ℝ => starobinskyV M alpha phi) (contDiff_starobinskyV M alpha)) := wallHam_essentiallySelfAdjoint _ _ (fun phi => starobinskyV_nonneg halpha phi)
