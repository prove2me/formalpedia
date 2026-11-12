-- Prove2me | solution 1 for ForecastAggLearn.barL_gradient_convex
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-11T12:19:02.293208+00:00
-- url     : https://prove2.me/submissions/3b71e126-c1f2-412f-8d2f-718f170f1a1c

import Definitions.Def_ForecastAggLearn_barL
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open ForecastAggLearn

private noncomputable def scalarLoss (a μ x : ℝ) := a * (x + μ) + Real.log (1 + Real.exp (-x - μ))
private noncomputable def scalarGrad (a μ x : ℝ) := a - Real.exp (-x - μ) / (1 + Real.exp (-x - μ))
private noncomputable def scalarHess (μ x : ℝ) := Real.exp (-x - μ) / (1 + Real.exp (-x - μ)) ^ 2

private theorem scalar_first (a μ x : ℝ) :
    HasDerivAt (scalarLoss a μ) (scalarGrad a μ x) x := by
  have hd := ((((hasDerivAt_id x).neg.sub_const μ).exp).const_add 1).log
    (show 1 + Real.exp (-x - μ) ≠ 0 by positivity)
  have hh := (((hasDerivAt_id x).add_const μ).const_mul a).add hd
  convert! hh using 1
  dsimp [scalarLoss, scalarGrad]
  ring

private theorem scalar_second (a μ x : ℝ) :
    HasDerivAt (scalarGrad a μ) (scalarHess μ x) x := by
  have he := ((hasDerivAt_id x).neg.sub_const μ).exp
  have hd := (he.div (he.const_add 1) (show 1 + Real.exp (-x - μ) ≠ 0 by positivity)).const_sub a
  convert! hd using 1
  dsimp [scalarGrad, scalarHess]
  ring

private theorem scalar_convex (a μ : ℝ) : ConvexOn ℝ Set.univ (scalarLoss a μ) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := scalarGrad a μ)
    (f'' := scalarHess μ) convex_univ
  · exact (continuous_iff_continuousAt.mpr (fun x => (scalar_first a μ x).continuousAt)).continuousOn
  · intro x _; exact (scalar_first a μ x).hasDerivWithinAt
  · intro x _; exact (scalar_second a μ x).hasDerivWithinAt
  · intro x _; exact div_nonneg (Real.exp_pos _).le (sq_nonneg _)

theorem solution {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (μt : ℝ) (ω : Bool) :
    (∀ h, HasGradientAt (barL z μt ω)
        ((if ω then (0 : ℝ) else 1) • z -
          (Real.exp (-(inner ℝ h z) - μt) / (1 + Real.exp (-(inner ℝ h z) - μt))) • z) h) ∧
      (∀ h, ‖(if ω then (0 : ℝ) else 1) • z -
          (Real.exp (-(inner ℝ h z) - μt) / (1 + Real.exp (-(inner ℝ h z) - μt))) • z‖ ≤ ‖z‖) ∧
      (∀ h v, 0 ≤ fderiv ℝ (fderiv ℝ (barL z μt ω)) h v v) ∧
      ConvexOn ℝ Set.univ (barL z μt ω) := by
  let a : ℝ := if ω then 0 else 1
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ z
  have heq : barL z μt ω = scalarLoss a μt ∘ L := by
    funext h
    simp [barL, scalarLoss, a, L, real_inner_comm]
  have hD (h : EuclideanSpace ℝ (Fin n)) :
      HasFDerivAt (barL z μt ω) (scalarGrad a μt (L h) • L) h := by
    rw [heq]
    convert! (scalar_first a μt (L h)).comp_hasFDerivAt h L.hasFDerivAt using 1
  have hDF : fderiv ℝ (barL z μt ω) = fun h => scalarGrad a μt (L h) • L :=
    funext fun h => (hD h).fderiv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rw [hasGradientAt_iff_hasFDerivAt]
    convert! hD h using 1
    ext v
    cases ω <;> simp [scalarGrad, a, L, InnerProductSpace.toDual_apply_apply, real_inner_comm,
      sub_mul]
  · intro h
    let q := Real.exp (-(inner ℝ h z) - μt) / (1 + Real.exp (-(inner ℝ h z) - μt))
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hq1 : q ≤ 1 := by dsimp [q]; apply (div_le_one (by positivity)).mpr; linarith
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have hcoeff : |a - q| ≤ 1 := by cases ω <;> dsimp [a] <;> rw [abs_le] <;> constructor <;> linarith
    simpa [a, q] using mul_le_mul_of_nonneg_right hcoeff (norm_nonneg z)
  · intro h v
    have hd : HasFDerivAt (fun h => scalarGrad a μt (L h)) (scalarHess μt (L h) • L) h := by
      convert! (scalar_second a μt (L h)).comp_hasFDerivAt h L.hasFDerivAt using 1
    rw [hDF, (hd.smul_const L).fderiv]
    change 0 ≤ scalarHess μt (L h) * L v * L v
    have hc : 0 ≤ scalarHess μt (L h) := div_nonneg (Real.exp_pos _).le (sq_nonneg _)
    nlinarith [mul_nonneg hc (sq_nonneg (L v))]
  · rw [heq]
    simpa using (scalar_convex a μt).comp_linearMap L.toLinearMap

#print axioms solution