-- Prove2me | solution 1 for BookProof.LimitCircleExample.exists_smooth_potential_not_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T05:50:31.693125+00:00
-- url     : https://prove2.me/submissions/a0b5ddcd-3be0-4852-9ca8-2e3e65de726e

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterWallDeficiencyObstruction
import Mathlib
import Theorems.Thm_BookProof_LimitCircleExample_contDiff_lcV
import Theorems.Thm_BookProof_LimitCircleExample_lcSol_isL2Ode
import Theorems.Thm_BookProof_LimitCircleExample_lcSol_ne_zero

import Definitions.Def_ChapterLimitCircleExample
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa
open BookProof.LimitCircleExample



open MeasureTheory Real
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction

noncomputable section

theorem solution :
    ∃ (V : ℝ → ℝ) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V),
      ¬ EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam V hV) :=
  ⟨BookProof.LimitCircleExample.lcV, BookProof.LimitCircleExample.contDiff_lcV,
    BookProof.WallDeficiencyObstruction.not_essentiallySelfAdjointOn_of_l2_solution _ _
      BookProof.LimitCircleExample.lcSol_isL2Ode ⟨0, BookProof.LimitCircleExample.lcSol_ne_zero 0⟩⟩
