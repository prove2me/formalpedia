-- Prove2me | solution 1 for BookProof.ScalaronDensitized.physConfOp_quadForm_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:07:46.653764+00:00
-- url     : https://prove2.me/submissions/50467223-1b3c-4b0c-bbd2-7c7d866b8f31

-- Generated from ChapterScalaronDensitizedTransfer.lean — solution of BookProof.ScalaronDensitized.physConfOp_quadForm_ge
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Theorems.Thm_BookProof_ScalaronDensitized_multOp_quadForm_ge
import Theorems.Thm_BookProof_Starobinsky_confV_ge
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.ScalaronDensitized




open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable (M alpha : ℝ)
variable {X : Type*} [MeasurableSpace X]

set_option maxHeartbeats 1000000 in
theorem solution (halpha : 0 < alpha) (f : physConfCore M alpha) :
    -(M ^ 4 / (16 * alpha)) * ‖(f : Lp ℂ 2 physMeasure)‖ ^ 2
      ≤ quadForm ((physConfCore M alpha).subtype.comp (physConfOp M alpha)) f :=
  multOp_quadForm_ge physMeasure (measurable_confV M alpha)
      (fun e => confV_ge halpha e) f
