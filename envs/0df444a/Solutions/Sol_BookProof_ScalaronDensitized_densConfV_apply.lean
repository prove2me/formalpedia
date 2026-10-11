-- Prove2me | solution 1 for BookProof.ScalaronDensitized.densConfV_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:56.23497+00:00
-- url     : https://prove2.me/submissions/f4ccf77a-08f8-4a89-a5f2-7d27350aaa01

-- Generated from ChapterScalaronDensitizedTransfer.lean — solution of BookProof.ScalaronDensitized.densConfV_apply
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.ScalaronDensitized




open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (M alpha y : ℝ) : densConfV M alpha y = confV M alpha (y ^ 2) := rfl
