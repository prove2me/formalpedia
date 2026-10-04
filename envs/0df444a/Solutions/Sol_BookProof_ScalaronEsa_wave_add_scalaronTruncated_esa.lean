-- Prove2me | solution 1 for BookProof.ScalaronEsa.wave_add_scalaronTruncated_esa
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:04:08.250044+00:00
-- url     : https://prove2.me/submissions/abebb527-57a6-425b-aeff-3284387e30a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.wave_add_scalaronTruncated_esa
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Theorems.Thm_BookProof_ScalaronEsa_contDiff_scalaronAlong
import Theorems.Thm_BookProof_ScalaronEsa_wave_add_smoothTruncatedPotential_essentiallySelfAdjoint
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

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (M alpha : ℝ) (e : SpaceTime n) (R : ℝ) :
    ∃ WR : SpaceTime n → ℝ, Function.HasTemperateGrowth WR ∧
      (∀ x, ‖x‖ ≤ R → WR x = starobinskyV M alpha (inner ℝ x e)) ∧
      (∀ x, R + 1 ≤ ‖x‖ → WR x = 0) ∧
      EssentiallySelfAdjointOn (schwartzDomain (SpaceTime n))
        (opL2 (waveOp n 0 + potentialOp WR)) :=
  wave_add_smoothTruncatedPotential_essentiallySelfAdjoint n _
      (contDiff_scalaronAlong M alpha e) R
