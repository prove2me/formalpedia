-- Prove2me | solution 1 for BookProof.ScalaronEsa.contDiff_scalaronAlong
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:43:24.629032+00:00
-- url     : https://prove2.me/submissions/cd8872a4-1e61-4bf3-a0d8-7272f8266d66

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.contDiff_scalaronAlong
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
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
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem solution (M alpha : ℝ) (e : E) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : E => starobinskyV M alpha (inner ℝ x e)) := (contDiff_starobinskyV M alpha).comp ((innerSL ℝ).flip e).contDiff
