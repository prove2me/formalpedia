-- Prove2me | solution 2 for BookProof.ScalaronEsa.starobinskyV_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:15:52.150467+00:00
-- url     : https://prove2.me/submissions/0cdf3923-8c1d-4e59-91ae-b6442b1ac92d

import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStrichartzWave
-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.starobinskyV_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_essentiallySelfAdjoint
import Theorems.Thm_BookProof_ScalaronEsa_contDiff_starobinskyV
open BookProof.ScalaronEsa



open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) :
    EssentiallySelfAdjointOn (ccDomain ℝ)
      (opCc (fun phi : ℝ => starobinskyV M alpha phi) (contDiff_starobinskyV M alpha)) := smoothPotential_essentiallySelfAdjoint _ _
