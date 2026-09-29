-- Prove2me | solution 1 for BookProof.ScalaronEsa.mulCc_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T13:44:29.844066+00:00
-- url     : https://prove2.me/submissions/6f6f9b6d-1beb-4fe7-b388-c2b27a2918be

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.mulCc_apply
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
    (f : ccSchwartz E) (x : E) :
    (mulCc W hW f) x = (W x : ℂ) * (f : 𝓢(E, ℂ)) x := rfl
