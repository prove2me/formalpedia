-- Prove2me | solution 1 for BookProof.ScalaronWallEsa.starobinskyWall_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:39:13.529173+00:00
-- url     : https://prove2.me/submissions/e0630830-dc55-4789-bbad-e87bf7aa5e5d

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
