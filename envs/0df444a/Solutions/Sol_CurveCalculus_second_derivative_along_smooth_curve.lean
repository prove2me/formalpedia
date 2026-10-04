-- Prove2me | solution 1 for CurveCalculus.second_derivative_along_smooth_curve
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T18:40:49.992981+00:00
-- url     : https://prove2.me/submissions/b8e27955-f52b-40bd-9e7f-05d2a476ac48

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.NormNum
open Set Filter
open scoped Topology ContDiff
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ) (γ : ℝ → E)
    (t0 : ℝ) (y v : E) (hγ : ContDiffAt ℝ ∞ γ t0) (hc : ContDiffAt ℝ ∞ F y)
    (hγ0 : γ t0 = y) (hγ1 : deriv γ t0 = v) :
    deriv (deriv (F ∘ γ)) t0 =
      fderiv ℝ (fun x => fderiv ℝ F x v) y v + fderiv ℝ F y (deriv (deriv γ) t0) := by
  have hdγ := (hγ.differentiableAt (by simp)).hasDerivAt
  have hdDγ := ((hγ.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hc.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hD := hDF.hasFDerivAt.comp_hasDerivAt_of_eq t0 hdγ hγ0.symm
  have hpair := hD.clm_apply hdDγ
  have heq : deriv (F ∘ γ) =ᶠ[nhds (t0 : ℝ)]
      (fun t => fderiv ℝ F (γ t) (deriv γ t)) := by
    have ht : Tendsto γ (nhds t0) (nhds y) := by simpa [hγ0] using hγ.continuousAt.tendsto
    have hγone : ContDiffAt ℝ 1 γ t0 := hγ.of_le (mod_cast le_top)
    have hFone : ContDiffAt ℝ 1 F y := hc.of_le (mod_cast le_top)
    filter_upwards [hγone.eventually (by norm_num),
      ht.eventually (hFone.eventually (by norm_num))] with t htγ htF
    exact htF.differentiableAt_one.hasFDerivAt.comp_hasDerivAt t
      (htγ.differentiableAt_one.hasDerivAt) |>.deriv
  have hhess : fderiv ℝ (fun x => fderiv ℝ F x v) y v =
      (fderiv ℝ (fderiv ℝ F) y v) v := by
    have h := (hDF.hasFDerivAt.clm_apply (hasFDerivAt_const v y)).fderiv
    simpa using DFunLike.congr_fun h v
  simpa only [Function.comp_apply, hγ0, hγ1, hhess] using (hpair.congr_of_eventuallyEq heq).deriv
