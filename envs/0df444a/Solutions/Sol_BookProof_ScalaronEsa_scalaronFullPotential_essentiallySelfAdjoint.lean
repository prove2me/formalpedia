-- Prove2me | solution 1 for BookProof.ScalaronEsa.scalaronFullPotential_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T22:29:35.981037+00:00
-- url     : https://prove2.me/submissions/0d7638c5-7b94-4096-84cf-8a81d2738db7

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.scalaronFullPotential_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_essentiallySelfAdjoint
import Theorems.Thm_BookProof_ScalaronEsa_contDiff_scalaronFullPotential
open BookProof.ScalaronEsa



open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (eRc ephi : E) :
    EssentiallySelfAdjointOn (ccDomain E)
      (opCc (scalaronFullPotential M alpha eRc ephi)
        (contDiff_scalaronFullPotential M alpha eRc ephi)) := smoothPotential_essentiallySelfAdjoint _ _
