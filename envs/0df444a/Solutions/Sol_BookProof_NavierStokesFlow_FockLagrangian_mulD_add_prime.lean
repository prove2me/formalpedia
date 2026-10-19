-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.mulD_add_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:02:11.860032+00:00
-- url     : https://prove2.me/submissions/b07e765f-f510-41d9-8570-23fc10af4ca6

-- Generated from ChapterNavierStokesFockLagrangian.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.mulD_add'
import Mathlib
import Definitions.Def_ChapterNavierStokesFockLagrangian
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian



open MeasureTheory



open FullEsa FockContinuum
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval

variable {X : Type*} [MeasurableSpace X]

variable {X : Type*} [MeasurableSpace X]

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure X) {g h₁ h₂ h : X → ℝ} (hh₁ : Measurable h₁)
    (hh₂ : Measurable h₂) (hh : Measurable h) (d₁ : DominatedOn μ g h₁)
    (d₂ : DominatedOn μ g h₂) (d : DominatedOn μ g h) (heq : ∀ x, h x = h₁ x + h₂ x) :
    mulD μ hh₁ d₁ + mulD μ hh₂ d₂ = mulD μ hh d := by

  rw [mulD_add μ hh₁ hh₂ d₁ d₂]
  exact mulD_congr μ (hh₁.add hh₂) hh (d₁.add d₂) d
    (Filter.Eventually.of_forall fun x => (heq x).symm)
