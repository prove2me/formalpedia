-- Prove2me | solution 1 for BookProof.ScalaronEsa.ccEquiv_coe
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T20:23:54.862478+00:00
-- url     : https://prove2.me/submissions/dda1640d-d68e-4dde-a529-307465cb3b80

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.ccEquiv_coe
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
    ((ccEquiv E f : ccDomain E) : Lp ℂ 2 (volume : Measure E))
      = (f : 𝓢(E, ℂ)).toLp 2 (volume : Measure E) := rfl
