-- Prove2me | solution 1 for BookProof.LimitCircleExample.lcV_not_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T14:56:27.346212+00:00
-- url     : https://prove2.me/submissions/abf24ccf-ff76-4433-8e7f-6692a9546ec4

-- Generated from ChapterLimitCircleExample.lean — solution of BookProof.LimitCircleExample.lcV_not_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterLimitCircleExample
import Theorems.Thm_BookProof_LimitCircleExample_lcSol_ne_zero
import Theorems.Thm_BookProof_LimitCircleExample_lcSol_isL2Ode
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterWallDeficiencyObstruction
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Theorems.Thm_BookProof_LimitCircleExample_contDiff_lcV
open BookProof.LimitCircleExample




open MeasureTheory Real
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution :
    ¬ EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam lcV contDiff_lcV) := not_essentiallySelfAdjointOn_of_l2_solution _ _ lcSol_isL2Ode ⟨0, lcSol_ne_zero 0⟩
