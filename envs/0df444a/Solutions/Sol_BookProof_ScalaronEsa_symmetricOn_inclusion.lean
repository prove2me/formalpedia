-- Prove2me | solution 1 for BookProof.ScalaronEsa.symmetricOn_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:43:27.62034+00:00
-- url     : https://prove2.me/submissions/0076c05b-b2ea-4cd5-9b7b-96f94a21790b

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.symmetricOn_inclusion
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
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {D D' : Submodule ℂ F} (h : D ≤ D') (T : D' →ₗ[ℂ] F) (hT : SymmetricOn D' T) :
    SymmetricOn D (T ∘ₗ Submodule.inclusion h) := by

  intro x y
  simpa using hT (Submodule.inclusion h x) (Submodule.inclusion h y)
