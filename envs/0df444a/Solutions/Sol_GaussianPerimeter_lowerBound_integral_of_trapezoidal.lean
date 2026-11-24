-- Prove2me | solution 1 for GaussianPerimeter.lowerBound_integral_of_trapezoidal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:25:53.381847+00:00
-- url     : https://prove2.me/submissions/f4d946c6-1f30-4ece-a731-1c8303be99d9

module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GaussianPerimeter_Quadrature
public import Theorems.Thm_GaussianPerimeter_lowerBound_trapezoidal_error
section
@[expose] public section
open Set
open scoped Interval
namespace GaussianPerimeter
private theorem integrand_contDiff (a b : ℝ) : ContDiff ℝ 2 (lowerBoundIntegrand a b) := by
  unfold lowerBoundIntegrand
  fun_prop
local notation "a₀" => (6131 / 5000 : ℝ)
local notation "b₀" => (2387 / 1000 : ℝ)
local notation "F" => lowerBoundIntegrand a₀ b₀
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped Interval
open GaussianPerimeter
local notation "a₀" => (6131 / 5000 : ℝ)
local notation "b₀" => (2387 / 1000 : ℝ)
local notation "F" => lowerBoundIntegrand a₀ b₀
namespace GaussianPerimeter
theorem _root_.solution
    (h : (0.3331065 : ℝ) ≤ trapezoidal_integral F 10240 (-(15 / 4)) (5 / 4)) :
    (0.333104 : ℝ) ≤ ∫ x in (-6 : ℝ)..6, F x := by
  have he := (abs_le.mp lowerBound_trapezoidal_error).2
  unfold trapezoidal_error at he
  calc
    _ ≤ ∫ x in (-(15 / 4) : ℝ)..(5 / 4), F x := by linarith
    _ ≤ _ := intervalIntegral.integral_mono_interval (by norm_num) (by norm_num)
      (by norm_num) (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))
      ((integrand_contDiff a₀ b₀).continuous.intervalIntegrable _ _)
end GaussianPerimeter
