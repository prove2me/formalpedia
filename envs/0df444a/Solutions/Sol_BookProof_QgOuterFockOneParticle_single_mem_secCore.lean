-- Prove2me | solution 1 for BookProof.QgOuterFockOneParticle.single_mem_secCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T13:19:06.418181+00:00
-- url     : https://prove2.me/submissions/c748d9de-abd1-429a-a569-bd830a173f54

-- Generated from ChapterQgOuterFockOneParticle.lean — solution of BookProof.QgOuterFockOneParticle.single_mem_secCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockOneParticle
import Theorems.Thm_BookProof_DirectSumEsa_single_mem_dsCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
open BookProof.QgOuterFockOneParticle




open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa

noncomputable section

variable {ι : Type*} [DecidableEq ι] (W : WallPot) (Q : QgModeData ι)

variable {ι : Type*} [DecidableEq ι] (W : WallPot) (Q : QgModeData ι)

set_option maxHeartbeats 1000000 in

theorem solution (b : ι) (u : ccDomain ℝ) :
    (lp.single 2 b ((u : L2R)) : Sec ι) ∈ secCore (ι := ι) :=
  single_mem_dsCore (G := fun _ : ι => L2R) (D := fun _ : ι => ccDomain ℝ) b u
