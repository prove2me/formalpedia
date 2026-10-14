-- Prove2me | solution 1 for DbarRegularity.cauchyRiemann_lp_complex
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:37:47.886214+00:00
-- url     : https://prove2.me/submissions/7a982fc7-39be-4142-8f42-084ba49f1f47

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Theorems.Thm_DbarRegularity_cauchyRiemann_lp_plane



namespace DbarRegularity

open MeasureTheory Metric
open scoped ENNReal NNReal

/-- For `1 < p < ∞` there is `A` such that every complex-valued `C¹` map `f : ℂ → ℂ` with compact
support satisfies `‖f_s‖_p + ‖f_t‖_p ≤ A ‖∂̄f‖_p`, where `z = s + i t`, `f_s = fderiv ℝ f z 1` and
`f_t = fderiv ℝ f z i`. -/
theorem cauchyRiemann_lp_complex_aux (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ f : ℂ → ℂ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (fun z => fderiv ℝ f z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ f z Complex.I) (ENNReal.ofReal p) volume
        ≤ A * eLpNorm (dbar f) (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA⟩ := cauchyRiemann_lp_plane p hp
  refine ⟨A, fun f hf hfc => ?_⟩
  set e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm with he
  have hmp : MeasurePreserving e volume volume := e.measurePreserving
  have he0 : e (EuclideanSpace.single 0 1) = 1 := by
    rw [he, Complex.orthonormalBasisOneI_repr_symm_apply]; simp
  have he1 : e (EuclideanSpace.single 1 1) = Complex.I := by
    rw [he, Complex.orthonormalBasisOneI_repr_symm_apply]; simp
  set g : EuclideanSpace ℝ (Fin 2) → ℂ := f ∘ e with hgdef
  have hg : ContDiff ℝ 1 g := hf.comp e.contDiff
  have hgc : HasCompactSupport g := hfc.comp_homeomorph e.toHomeomorph
  have hd : ∀ x v, fderiv ℝ g x v = fderiv ℝ f (e x) (e v) := by
    intro x v
    have := e.toContinuousLinearEquiv.comp_right_fderiv (f := f) (x := x)
    rw [hgdef]
    exact congrArg (fun L => L v) this
  have h := hA g hg hgc
  simp only [hd, he0, he1] at h
  have hc := hf.continuous_fderiv (by norm_num)
  have hc1 : Continuous fun z => fderiv ℝ f z 1 := by fun_prop
  have hcI : Continuous fun z => fderiv ℝ f z Complex.I := by fun_prop
  have hcd : Continuous (dbar f) := by
    unfold dbar; fun_prop
  have k1 := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal p) hc1.aestronglyMeasurable hmp
  have kI := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal p) hcI.aestronglyMeasurable hmp
  have kd := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal p) hcd.aestronglyMeasurable hmp
  have hdb : (fun x => fderiv ℝ f (e x) 1 + Complex.I * fderiv ℝ f (e x) Complex.I)
      = dbar f ∘ e := by
    funext x; simp [dbar, Function.comp]
  rw [hdb, kd] at h
  simp only [Function.comp_def] at k1 kI
  rw [k1, kI] at h
  exact h

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric
open scoped ENNReal NNReal

theorem solution (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ f : ℂ → ℂ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (fun z => fderiv ℝ f z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ f z Complex.I) (ENNReal.ofReal p) volume
        ≤ A * eLpNorm (dbar f) (ENNReal.ofReal p) volume :=
  cauchyRiemann_lp_complex_aux p hp
