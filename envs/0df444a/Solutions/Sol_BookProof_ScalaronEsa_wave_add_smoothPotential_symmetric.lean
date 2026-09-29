-- Prove2me | solution 1 for BookProof.ScalaronEsa.wave_add_smoothPotential_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:46:58.37754+00:00
-- url     : https://prove2.me/submissions/22cd6dd8-cd02-4656-8888-3c2cee1678ae

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.wave_add_smoothPotential_symmetric
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_symmetric
import Theorems.Thm_BookProof_ScalaronEsa_waveCc_symmetric
open BookProof.ScalaronEsa



open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (W : SpaceTime n → ℝ)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    SymmetricOn (ccDomain (SpaceTime n)) (waveAddSmoothPotential n W hW) := by

  intro x y
  have h1 := waveCc_symmetric n x y
  have h2 := smoothPotential_symmetric W hW x y
  simp only [waveAddSmoothPotential, LinearMap.add_apply, inner_add_left, inner_add_right]
  linear_combination h1 + h2
