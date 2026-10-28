-- Prove2me | solution 1 for D1Bound5.ordinary_integer_orders_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:51:03.540722+00:00
-- url     : https://prove2.me/submissions/f186887c-cc88-4821-9068-3986d856beb8

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

section
namespace D1Bound5

/-- Selecting the actual positive integer order from the logarithmic
floor gives a division-free logarithmic inequality. This is the scalar
step from all integer orders to the ordinary height envelope. -/
theorem _root_.solution (H R Z X : ℝ)
    (hH : 1 ≤ H) (hR : 1 < R) (hZ : 1 ≤ Z) (hX : 0 < X)
    (horders : ∀ k : ℕ, 1 ≤ k → 1 < X*H^k/Z+Z/(2*R^k)) :
    Real.log Z*(Real.log R-Real.log H) < Real.log (2*X*H)*Real.log R := by
  have hH0 : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hR0 : 0 < R := lt_trans (by norm_num) hR
  have hZ0 : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hlR : 0 < Real.log R := Real.log_pos hR
  have hlH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hlZ : 0 ≤ Real.log Z := Real.log_nonneg hZ
  let k : ℕ := ⌊Real.log Z/Real.log R⌋₊+1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hklo : Real.log Z < (k : ℝ)*Real.log R := by
    have h := Nat.lt_floor_add_one (Real.log Z/Real.log R)
    have h' : Real.log Z/Real.log R < (k : ℝ) := by
      simpa only [k,Nat.cast_add,Nat.cast_one] using h
    exact (div_lt_iff₀ hlR).mp h'
  have hkhi : (k : ℝ)*Real.log R ≤ Real.log Z+Real.log R := by
    have h := Nat.floor_le (div_nonneg hlZ hlR.le)
    have h' : (k : ℝ) ≤ Real.log Z/Real.log R+1 := by
      simp only [k,Nat.cast_add,Nat.cast_one]
      linarith only [h]
    have hm := mul_le_mul_of_nonneg_right h' hlR.le
    have heq : (Real.log Z/Real.log R+1)*Real.log R = Real.log Z+Real.log R := by
      field_simp [hlR.ne']
    rwa [heq] at hm
  have hZR : Z < R^k := by
    apply (Real.log_lt_log_iff hZ0 (pow_pos hR0 k)).mp
    simpa only [Real.log_pow] using hklo
  have hres : Z/(2*R^k) < (1/2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*R^k)).mpr
    nlinarith only [hZR]
  have hfirst : (1/2 : ℝ) < X*H^k/Z := by
    have h := horders k hk
    linarith only [h,hres]
  have hheight : Z < 2*X*H^k := by
    have h := (lt_div_iff₀ hZ0).mp hfirst
    nlinarith only [h]
  have hlog := Real.log_lt_log hZ0 hheight
  rw [Real.log_mul (by positivity : (2:ℝ)*X ≠ 0) (pow_ne_zero k hH0.ne'),
    Real.log_pow] at hlog
  have hp := mul_lt_mul_of_pos_right hlog hlR
  have hq := mul_le_mul_of_nonneg_left hkhi hlH
  rw [Real.log_mul (by positivity : (2:ℝ)*X ≠ 0) hH0.ne']
  nlinarith only [hp,hq]





end D1Bound5
end
