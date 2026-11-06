-- Prove2me | solution 1 for BookProof.QgVielbeinModeInstance.qgLattice_ext_core
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:34:29.615902+00:00
-- url     : https://prove2.me/submissions/a863400f-73fc-4f05-beef-c1380d670a54

import Definitions.Def_ChapterQgVielbeinModeInstance

open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.ScalaronFiberFL
open BookProof.ScalaronFiberFL.WallPot
open BookProof.QgVielbeinModeInstance
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

variable {ι : Type*}

variable [Fintype ι] [DecidableEq ι]
variable (L : ℕ) [NeZero L]

theorem solution (W : WallPot) (sig : VMode L → ℝ) (hsig : ∀ a, 1 ≤ sig a) (g : ℝ)
    (p : secCore (ι := VMode L)) :
    (secData W (qgLatticeModes L sig hsig g)).ext
        ⟨(p : Sec (VMode L)), (secData W (qgLatticeModes L sig hsig g)).gc.le p.2⟩
      = secHam W (qgLatticeModes L sig hsig g) p := by
  exact secData_ext_core W (qgLatticeModes L sig hsig g) p
