-- Prove2me | solution 1 for BookProof.ScalaronEsa.mem_ccSchwartz
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:56:09.296893+00:00
-- url     : https://prove2.me/submissions/0a045b28-cea8-4a63-8d03-c1cbd4790c9c

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

theorem solution {f : 𝓢(E, ℂ)} :
    f ∈ ccSchwartz E ↔ HasCompactSupport (f : E → ℂ) := Iff.rfl

end
