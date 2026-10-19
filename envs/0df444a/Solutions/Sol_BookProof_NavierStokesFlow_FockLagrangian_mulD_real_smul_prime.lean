-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.mulD_real_smul_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:02:13.260982+00:00
-- url     : https://prove2.me/submissions/1052711d-378c-4ebf-9c3e-2f04b048c5f6

-- Generated from ChapterNavierStokesFockLagrangian.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.mulD_real_smul'
import Mathlib
import Definitions.Def_ChapterNavierStokesFockLagrangian
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian



open MeasureTheory



open FullEsa FockContinuum

variable {X : Type*} [MeasurableSpace X]

variable {X : Type*} [MeasurableSpace X]

set_option maxHeartbeats 1000000 in
theorem solution (μ : Measure X) {g h₁ h : X → ℝ} (r : ℝ) (hh₁ : Measurable h₁)
    (hh : Measurable h) (d₁ : DominatedOn μ g h₁) (d : DominatedOn μ g h)
    (heq : ∀ x, h x = r * h₁ x) :
    ((r : ℝ) : ℂ) • mulD μ hh₁ d₁ = mulD μ hh d := by

  rw [mulD_real_smul μ r hh₁ d₁]
  exact mulD_congr μ ((measurable_const (a := r)).mul hh₁) hh
    (DominatedOn.const_mul r d₁) d (Filter.Eventually.of_forall fun x => (heq x).symm)
