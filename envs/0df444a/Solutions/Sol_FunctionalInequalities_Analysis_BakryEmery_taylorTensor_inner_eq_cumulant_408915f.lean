-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.taylorTensor_inner_eq_cumulant_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:49:32.164352+00:00
-- url     : https://prove2.me/submissions/ab12df52-513b-458e-8f7c-841cd1f24bc1

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tiltAverage_inner_eq_fderiv_logLaplace_408915f

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section LaplaceCalculus
omit [CompleteSpace E]
section NormedSpace
variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma FunctionalInequalities.Analysis.BakryEmery.bkl_cumulant_swap_front [CompleteSpace F] {g : E → F} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x v w : E) (h : Fin n → E) :
    iteratedFDeriv ℝ (n + 2) g x (Fin.cons v (Fin.cons w h)) =
      iteratedFDeriv ℝ (n + 2) g x (Fin.cons w (Fin.cons v h)) := by
  have hd : ContDiff ℝ ∞ (iteratedFDeriv ℝ n g) :=
    hg.iteratedFDeriv_right (m := ∞) (by norm_cast)
  have ha : ContDiff ℝ ∞ (fun y => iteratedFDeriv ℝ n g y h) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F h).contDiff.comp hd
  have heq (a : E) :
      (fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.cons a h)) =
        fun y => fderiv ℝ (fun z => iteratedFDeriv ℝ n g z h) y a := by
    funext y
    simpa using (hd.differentiable (by simp) y).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons a h)
  have hleft :=
    (hg.differentiable_iteratedFDeriv (m := n + 1)
      (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons v (Fin.cons w h))
  have hright :=
    (hg.differentiable_iteratedFDeriv (m := n + 1)
      (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left'
      (m := Fin.cons w (Fin.cons v h))
  rw [hleft, hright]
  simp only [Fin.tail_cons, Fin.cons_zero]
  rw [heq w, heq v]
  rw [fderiv_clm_apply
      (ha.fderiv_right (m := ∞) (by simp) |>.differentiable (by norm_num) x)
      (differentiableAt_const w),
    fderiv_clm_apply
      (ha.fderiv_right (m := ∞) (by simp) |>.differentiable (by norm_num) x)
      (differentiableAt_const v)]
  simpa using
    ((ha.of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)).contDiffAt.isSymmSndFDerivAt
      (by simp)).eq v w
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private lemma FunctionalInequalities.Analysis.BakryEmery.bkl_cumulant_cons_snoc [CompleteSpace F] {g : E → F} (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (x v : E) (h : Fin n → E) :
    iteratedFDeriv ℝ (n + 1) g x (Fin.cons v h) =
      iteratedFDeriv ℝ (n + 1) g x (Fin.snoc h v) := by
  induction n generalizing x with
  | zero =>
      congr 1
      ext i
      fin_cases i
      simp [Fin.snoc_zero]
  | succ n ih =>
      rw [← Fin.cons_self_tail h]
      rw [bkl_cumulant_swap_front hg n x v (h 0) (Fin.tail h)]
      rw [← Fin.cons_snoc_eq_snoc_cons]
      have heq :
          (fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.cons v (Fin.tail h))) =
            fun y => iteratedFDeriv ℝ (n + 1) g y (Fin.snoc (Fin.tail h) v) := by
        funext y
        exact ih y (Fin.tail h)
      rw [(hg.differentiable_iteratedFDeriv (m := n + 1)
          (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left',
        (hg.differentiable_iteratedFDeriv (m := n + 1)
          (by norm_cast; simp) x).iteratedFDeriv_succ_apply_left']
      simpa only [Fin.tail_cons, Fin.cons_zero] using
        congrArg (fun a : E → F => fderiv ℝ a x (h 0)) heq
end NormedSpace
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **Taylor tensors of linear functions are cumulants** (proof of BKL Proposition 7.1):
for `ℓ = ⟪v, ·⟫`, `T_d ℓ = κ_{d+1}(v, ·, …, ·) / d!`. -/
theorem solution (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v : E) (d : ℕ)
    (h : Fin d → E) :
    FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ (fun x => ⟪v, x⟫) d h = (d.factorial : ℝ)⁻¹ * FunctionalInequalities.Analysis.BakryEmery.cumulant μ (d + 1) (Fin.cons v h) := by
  have heq : FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ (fun x => ⟪v, x⟫) =
      fun z => fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) z v := by
    funext z
    exact FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_408915f μ hexp v z
  have hL := FunctionalInequalities.Analysis.BakryEmery.contDiff_logLaplace μ hexp
  have hd : ContDiff ℝ ∞ (fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ)) :=
    hL.fderiv_right (by simp)
  have hder :
      iteratedFDeriv ℝ d (fun z => fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) z v) 0 h =
        iteratedFDeriv ℝ d (fderiv ℝ (FunctionalInequalities.Analysis.BakryEmery.logLaplace μ)) 0 h v :=
    iteratedFDeriv_clm_apply_const_apply hd (by norm_cast; simp)
  simp only [FunctionalInequalities.Analysis.BakryEmery.taylorTensor, smul_apply, smul_eq_mul, heq]
  rw [hder]
  have hs := bkl_cumulant_cons_snoc hL d 0 v h
  have ht := iteratedFDeriv_succ_apply_right
    (𝕜 := ℝ) (f := FunctionalInequalities.Analysis.BakryEmery.logLaplace μ) (x := (0 : E)) (Fin.snoc h v)
  simp only [Fin.init_snoc, Fin.snoc_last] at ht
  rw [ht] at hs
  exact congrArg (fun a : ℝ => (d.factorial : ℝ)⁻¹ * a) hs.symm
