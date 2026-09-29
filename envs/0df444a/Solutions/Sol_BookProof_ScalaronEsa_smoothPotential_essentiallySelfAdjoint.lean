-- Prove2me | solution 1 for BookProof.ScalaronEsa.smoothPotential_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:47:44.278378+00:00
-- url     : https://prove2.me/submissions/088f3ec0-4431-4f95-84a0-9acfad7fc2c3

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.smoothPotential_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_deficiencyTrivial
open BookProof.ScalaronEsa



open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (W : E → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    EssentiallySelfAdjointOn (ccDomain E) (opCc W hW) :=
  ⟨smoothPotential_deficiencyTrivial W hW (by simp),
      smoothPotential_deficiencyTrivial W hW (by simp)⟩
