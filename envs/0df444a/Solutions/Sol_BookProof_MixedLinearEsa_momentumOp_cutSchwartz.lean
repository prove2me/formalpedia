-- Prove2me | solution 1 for BookProof.MixedLinearEsa.momentumOp_cutSchwartz
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:59:41.815887+00:00
-- url     : https://prove2.me/submissions/482c1349-836c-443b-9c4d-2daded006808
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.momentumOp_cutSchwartz
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Theorems.Thm_BookProof_MixedLinearEsa_momentumOp_apply
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFourierMultiplierEsa
open BookProof.MixedLinearEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (m : V) (g : V → ℝ) (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgcs : HasCompactSupport g) (f : 𝓢(V, ℂ)) (x : V) :
    (momentumOp m (cutSchwartz g hg hgcs f)) x
      = -Complex.I * (f x * ((fderiv ℝ g x m : ℝ) : ℂ))
        + ((g x : ℝ) : ℂ) * (momentumOp m f x) := by

  have hgc : DifferentiableAt ℝ (fun y : V => ((g y : ℝ) : ℂ)) x :=
    (Complex.ofRealCLM.differentiable.comp (hg.differentiable (by simp))).differentiableAt
  have hfd : DifferentiableAt ℝ (f : V → ℂ) x := f.differentiableAt
  have hprod : fderiv ℝ ((cutSchwartz g hg hgcs f) : V → ℂ) x
      = (((g x : ℝ) : ℂ)) • fderiv ℝ (f : V → ℂ) x
        + (f x) • fderiv ℝ (fun y : V => ((g y : ℝ) : ℂ)) x := by
    have hco : ((cutSchwartz g hg hgcs f) : V → ℂ) = fun y => ((g y : ℝ) : ℂ) * f y := rfl
    rw [hco, fderiv_fun_mul hgc hfd]
  have hcast : fderiv ℝ (fun y : V => ((g y : ℝ) : ℂ)) x m = ((fderiv ℝ g x m : ℝ) : ℂ) := by
    have h1 : HasFDerivAt (fun y : V => ((g y : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (fderiv ℝ g x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x
        ((hg.differentiable (by simp)).differentiableAt.hasFDerivAt)
    rw [h1.fderiv]
    rfl
  rw [momentumOp_apply, hprod]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hcast,
    momentumOp_apply]
  ring
