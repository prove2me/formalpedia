-- Prove2me | solution 2 for BookProof.ScalaronEsa.waveCc_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:13:51.637002+00:00
-- url     : https://prove2.me/submissions/85de6d1d-80ea-4f52-a97b-5fff451fd8e5

import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStrichartzWave
-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.waveCc_symmetric
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Theorems.Thm_BookProof_ScalaronEsa_symmetricOn_inclusion
import Theorems.Thm_BookProof_StrichartzWave_wave_symmetric
open BookProof.ScalaronEsa



open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) : SymmetricOn (ccDomain (SpaceTime n)) (waveCc n) := symmetricOn_inclusion _ _ (wave_symmetric n 0)
