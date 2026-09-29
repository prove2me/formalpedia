-- Prove2me | solution 1 for BookProof.ScalaronEsa.opCc_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T20:23:55.847599+00:00
-- url     : https://prove2.me/submissions/a2c2e12a-7b4c-4b58-ad4d-b58082b1d000

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.opCc_apply
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
theorem solution (W : E → ℝ) (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (f : ccSchwartz E) :
    opCc W hW (ccEquiv E f) = (mulCc W hW f).toLp 2 (volume : Measure E) := by

  simp [opCc]
