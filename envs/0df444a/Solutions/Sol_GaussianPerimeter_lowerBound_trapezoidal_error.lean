-- Prove2me | solution 1 for GaussianPerimeter.lowerBound_trapezoidal_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:24:36.292448+00:00
-- url     : https://prove2.me/submissions/abd46028-ae10-4a73-83d6-e78baff596d2

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
section
@[expose] public section
open Set
open scoped Interval
namespace GaussianPerimeter
private theorem integrand_contDiff (a b : ℝ) : ContDiff ℝ 2 (lowerBoundIntegrand a b) := by
  unfold lowerBoundIntegrand
  fun_prop
private theorem integrand_hasDeriv (a b x : ℝ) :
    HasDerivAt (lowerBoundIntegrand a b)
      ((-(2 * x) - a ^ 2 * (b * Real.exp (a ^ 2 * x))) * lowerBoundIntegrand a b x) x := by
  have h₁ : HasDerivAt (fun t : ℝ => a ^ 2 * t) (a ^ 2) x := by
    simpa using (hasDerivAt_id x).const_mul (a ^ 2)
  have h₂ := ((hasDerivAt_id x).pow 2).neg.sub (h₁.exp.const_mul b)
  convert h₂.exp using 1 <;> try rfl
  change _ * Real.exp (-x ^ 2 - b * Real.exp (a ^ 2 * x)) =
    Real.exp (-x ^ 2 - b * Real.exp (a ^ 2 * x)) * _
  simp only [id_eq]
  ring
private theorem integrand_secondDeriv (a b x : ℝ) :
    iteratedDeriv 2 (lowerBoundIntegrand a b) x =
      (((2 * x + a ^ 2 * (b * Real.exp (a ^ 2 * x))) ^ 2) -
        (2 + a ^ 4 * (b * Real.exp (a ^ 2 * x)))) * lowerBoundIntegrand a b x := by
  have h₁ : HasDerivAt (fun t : ℝ => a ^ 2 * t) (a ^ 2) x := by
    simpa using (hasDerivAt_id x).const_mul (a ^ 2)
  have h₂ := ((hasDerivAt_id x).const_mul 2).neg.sub
    ((h₁.exp.const_mul b).const_mul (a ^ 2))
  have h₃ := h₂.mul (integrand_hasDeriv a b x)
  change HasDerivAt (fun t => (-(2 * t) - a ^ 2 * (b * Real.exp (a ^ 2 * t))) *
    lowerBoundIntegrand a b t) _ x at h₃
  rw [iteratedDeriv_succ (n := 1), iteratedDeriv_one]
  simp_rw [show deriv (lowerBoundIntegrand a b) =
    (fun t => (-(2 * t) - a ^ 2 * (b * Real.exp (a ^ 2 * t))) * lowerBoundIntegrand a b t) from
      funext (fun t => (integrand_hasDeriv a b t).deriv)]
  rw [h₃.deriv]
  change (-(2 * 1) - a ^ 2 * (b * (Real.exp (a ^ 2 * x) * a ^ 2))) * _ +
    (-(2 * x) - a ^ 2 * (b * Real.exp (a ^ 2 * x))) * _ = _
  ring
private theorem nonneg_mul_exp_neg_le_one {x : ℝ} (hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 1 := by
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_one (Real.exp_pos x)).mpr (by simpa using Real.pow_div_factorial_le_exp x hx 1)
private theorem sq_mul_exp_neg_le_two {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ 2 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos x)]
  have h := Real.pow_div_factorial_le_exp x hx 2
  norm_num [Nat.factorial] at h
  linarith
local notation "a₀" => (6131 / 5000 : ℝ)
local notation "b₀" => (2387 / 1000 : ℝ)
local notation "F" => lowerBoundIntegrand a₀ b₀
private theorem integrand_secondDeriv_bound (x : ℝ) : |iteratedDeriv 2 F x| ≤ 22 := by
  rw [integrand_secondDeriv]
  set y := b₀ * Real.exp (a₀ ^ 2 * x) with hy
  let p := Real.exp (-(x ^ 2))
  let q := Real.exp (-y)
  have hy₀ : 0 ≤ y := by rw [hy]; positivity
  have hp₀ : 0 ≤ p := (Real.exp_pos _).le
  have hq₀ : 0 ≤ q := (Real.exp_pos _).le
  have hp : p ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  have hq : q ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy₀)
  have hF : F x = p * q := by
    rw [lowerBoundIntegrand, ← hy, sub_eq_add_neg, Real.exp_add]
  have hF₀ : 0 ≤ F x := (Real.exp_pos _).le
  have hF₁ : F x ≤ 1 := by rw [hF]; nlinarith [mul_nonneg (sub_nonneg.mpr hp) hq₀]
  have hxF : x ^ 2 * F x ≤ 1 := by
    rw [hF, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right (nonneg_mul_exp_neg_le_one (sq_nonneg x)) hq₀).trans
      (by simpa using hq)
  have hyF : y * F x ≤ 1 := by
    rw [hF, mul_comm p q, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right (nonneg_mul_exp_neg_le_one hy₀) hp₀).trans
      (by simpa using hp)
  have hyyF : y ^ 2 * F x ≤ 2 := by
    rw [hF, mul_comm p q, ← mul_assoc]
    calc
      y ^ 2 * q * p ≤ y ^ 2 * q * 1 :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (sq_nonneg _) hq₀)
      _ ≤ 2 := by simpa using sq_mul_exp_neg_le_two hy₀
  have hsquare :
      (2 * x + a₀ ^ 2 * y) ^ 2 ≤ 8 * x ^ 2 + (2 * a₀ ^ 4) * y ^ 2 := by
    nlinarith only [sq_nonneg (2 * x - a₀ ^ 2 * y)]
  have hfirst :
      (2 * x + a₀ ^ 2 * y) ^ 2 * F x ≤ 8 + 4 * a₀ ^ 4 := by
    calc
      _ ≤ (8 * x ^ 2 + (2 * a₀ ^ 4) * y ^ 2) * F x :=
        mul_le_mul_of_nonneg_right hsquare hF₀
      _ = 8 * (x ^ 2 * F x) + (2 * a₀ ^ 4) * (y ^ 2 * F x) := by ring
      _ ≤ 8 + 4 * a₀ ^ 4 := by
        norm_num at *
        linarith
  have hsecond : (2 + a₀ ^ 4 * y) * F x ≤ 2 + a₀ ^ 4 := by
    calc
      _ = 2 * F x + a₀ ^ 4 * (y * F x) := by ring
      _ ≤ 2 + a₀ ^ 4 := by norm_num at *; linarith
  have hfirst₀ : 0 ≤ (2 * x + a₀ ^ 2 * y) ^ 2 * F x :=
    mul_nonneg (sq_nonneg _) hF₀
  have hsecond₀ : 0 ≤ (2 + a₀ ^ 4 * y) * F x := by positivity
  rw [sub_mul, abs_le]
  constructor <;> norm_num at hfirst hsecond ⊢ <;> linarith
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
theorem _root_.solution :
    |trapezoidal_error F 10240 (-(15 / 4)) (5 / 4)| ≤ (0.00000219 : ℝ) := by
  have hlt : (-(15 / 4) : ℝ) < 5 / 4 := by norm_num
  have hd : ∀ x, |iteratedDerivWithin 2 F [[-(15 / 4), 5 / 4]] x| ≤ (22 : ℝ) := by
    intro x
    rw [uIcc_of_lt hlt]
    by_cases hx : x ∈ Icc (-(15 / 4)) (5 / 4)
    · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt)
        (integrand_contDiff a₀ b₀).contDiffAt hx]
      exact integrand_secondDeriv_bound x
    · rw [iteratedDerivWithin_succ (n := 1),
        derivWithin_zero_of_notMem_closure (by rwa [closure_Icc])]
      norm_num
  have h := trapezoidal_error_le_of_c2 (integrand_contDiff a₀ b₀).contDiffOn hd
    (N := 10240) (by decide)
  apply h.trans
  norm_num
end GaussianPerimeter
