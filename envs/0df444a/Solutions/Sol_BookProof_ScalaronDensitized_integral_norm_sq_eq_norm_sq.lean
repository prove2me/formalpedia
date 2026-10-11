-- Prove2me | solution 1 for BookProof.ScalaronDensitized.integral_norm_sq_eq_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:07:29.827168+00:00
-- url     : https://prove2.me/submissions/3bae0736-1ba8-4a04-b7c2-dc10250bfe1f

-- Generated from ChapterScalaronDensitizedTransfer.lean — solution of BookProof.ScalaronDensitized.integral_norm_sq_eq_norm_sq
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ScalaronDensitized




open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable (M alpha : ℝ)
variable {X : Type*} [MeasurableSpace X]

set_option maxHeartbeats 1000000 in
theorem solution (mu : Measure X) (f : Lp ℂ 2 mu) :
    ∫ a, ‖(f : X → ℂ) a‖ ^ 2 ∂mu = ‖f‖ ^ 2 := by

  have key : ∀ z : ℂ, (inner ℂ z z : ℂ) = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have h1 : (inner ℂ f f : ℂ) = ∫ a, (inner ℂ ((f : X → ℂ) a) ((f : X → ℂ) a) : ℂ) ∂mu :=
    L2.inner_def f f
  have h2 : (inner ℂ f f : ℂ) = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have h3 : ∫ a, (inner ℂ ((f : X → ℂ) a) ((f : X → ℂ) a) : ℂ) ∂mu
      = ((∫ a, ‖(f : X → ℂ) a‖ ^ 2 ∂mu : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => key _)
  rw [h3] at h1
  rw [h1] at h2
  exact_mod_cast h2
