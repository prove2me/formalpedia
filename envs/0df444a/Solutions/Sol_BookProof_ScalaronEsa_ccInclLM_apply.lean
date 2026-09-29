-- Prove2me | solution 1 for BookProof.ScalaronEsa.ccInclLM_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:43:23.393754+00:00
-- url     : https://prove2.me/submissions/5338eaf0-479c-4a06-9046-d53b0dca3672

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.ccInclLM_apply
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
open BookProof.ScalaronEsa



open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (f : ccSchwartz E) :
    ccInclLM E f = ((f : 𝓢(E, ℂ)).toLp 2 (volume : Measure E)) := rfl
