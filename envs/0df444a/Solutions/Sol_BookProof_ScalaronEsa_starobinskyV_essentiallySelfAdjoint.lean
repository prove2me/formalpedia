-- Prove2me | solution 1 for BookProof.ScalaronEsa.starobinskyV_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:48:52.8665+00:00
-- url     : https://prove2.me/submissions/7dd243bc-e70f-4094-a6c6-a3a6546dad66

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
