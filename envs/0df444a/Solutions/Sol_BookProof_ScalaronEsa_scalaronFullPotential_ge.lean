-- Prove2me | solution 1 for BookProof.ScalaronEsa.scalaronFullPotential_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:43:25.580372+00:00
-- url     : https://prove2.me/submissions/85e9c5a5-e932-41c3-9637-3acb498aa6e5

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.scalaronFullPotential_ge
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Theorems.Thm_BookProof_Starobinsky_confV_ge
import Theorems.Thm_BookProof_Starobinsky_starobinskyV_nonneg
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
theorem solution {M alpha : ℝ} (halpha : 0 < alpha) (eRc ephi : E) (x : E) :
    -(M ^ 4 / (16 * alpha)) ≤ scalaronFullPotential M alpha eRc ephi x := by

  have h1 := confV_ge (M := M) halpha (inner ℝ x eRc)
  have h2 := starobinskyV_nonneg (M := M) halpha (inner ℝ x ephi)
  simp only [scalaronFullPotential]
  linarith
