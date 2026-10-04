-- Prove2me | solution 1 for BookProof.ScalaronEsa.qgScalaronMode_deficiencyTrivialAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:51:34.300388+00:00
-- url     : https://prove2.me/submissions/7faed044-8044-4021-9b11-0f376f5044cc

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.qgScalaronMode_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Theorems.Thm_BookProof_QuantumGravityDensitized_qgModeHamiltonian_deficiencyTrivialAt
open BookProof.ScalaronEsa



open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (a b : ℕ → ℝ) (M alpha : ℝ) (Rc phi : ℕ → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt
      (mulSymbolDomain (qgModeSymbol a b (qgScalaronModePotential M alpha Rc phi)))
      (qgScalaronModeHamiltonian a b M alpha Rc phi) z := qgModeHamiltonian_deficiencyTrivialAt a b (qgScalaronModePotential M alpha Rc phi) hz
