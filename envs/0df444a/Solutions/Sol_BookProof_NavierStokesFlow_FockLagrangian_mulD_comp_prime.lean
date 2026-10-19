-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.mulD_comp_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:02:10.689982+00:00
-- url     : https://prove2.me/submissions/8105ada8-c5c9-4907-b967-8d1a967d4f63

-- Generated from ChapterNavierStokesFockLagrangian.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.mulD_comp'
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
    (d₂ : DominatedOn μ g h₂) (d : DominatedOn μ g h) (heq : ∀ x, h x = h₁ x * h₂ x) :
    (mulD μ hh₁ d₁).comp (mulD μ hh₂ d₂) = mulD μ hh d := by

  rw [mulD_comp μ hh₁ hh₂ d₁ d₂]
  exact mulD_congr μ (hh₁.mul hh₂) hh (d₁.mul d₂) d
    (Filter.Eventually.of_forall fun x => (heq x).symm)
