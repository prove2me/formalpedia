-- Prove2me | solution 1 for BookProof.QgVielbeinModeInstance.starobinsky_qgLattice_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-27T06:01:40.157658+00:00
-- url     : https://prove2.me/submissions/71fd9fe6-28f6-4e9d-9cea-a90bd2fe3a26

-- Generated from ChapterQgVielbeinModeInstance.lean — solution of BookProof.QgVielbeinModeInstance.starobinsky_qgLattice_esa
import Mathlib
import Definitions.Def_ChapterQgVielbeinModeInstance
import Theorems.Thm_BookProof_QgVielbeinModeInstance_qgLattice_essentiallySelfAdjointOn
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.QgVielbeinModeInstance




open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData

noncomputable section

variable {ι : Type*}

variable {ι : Type*}
variable [Fintype ι] [DecidableEq ι]
variable (L : ℕ) [NeZero L]

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (halpha : 0 < alpha) (sig : VMode L → ℝ)
    (hsig : ∀ a, 1 ≤ sig a) (g : ℝ) :
    EssentiallySelfAdjointOn
        (secN (starobinskyWall M alpha halpha) (qgLatticeModes L sig hsig g)).dom
      (secData (starobinskyWall M alpha halpha) (qgLatticeModes L sig hsig g)).ext := qgLattice_essentiallySelfAdjointOn L (starobinskyWall M alpha halpha) sig hsig g
