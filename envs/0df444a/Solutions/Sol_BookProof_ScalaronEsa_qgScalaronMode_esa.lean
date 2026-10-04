-- Prove2me | solution 1 for BookProof.ScalaronEsa.qgScalaronMode_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:51:38.05402+00:00
-- url     : https://prove2.me/submissions/ef5f9cd7-a135-467f-af79-dbad78ce7cf7

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.qgScalaronMode_esa
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Theorems.Thm_BookProof_QuantumGravityDensitized_qgModeHamiltonian_essentiallySelfAdjoint
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
theorem solution :
    EssentiallySelfAdjointOn
      (mulSymbolDomain (qgModeSymbol a b (qgScalaronModePotential M alpha Rc phi)))
      (qgScalaronModeHamiltonian a b M alpha Rc phi) := qgModeHamiltonian_essentiallySelfAdjoint a b (qgScalaronModePotential M alpha Rc phi)
