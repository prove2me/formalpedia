-- Prove2me | solution 1 for DataTrackComp.Surplus.gamma_eq_J1_div_J2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:53:03.916143+00:00
-- url     : https://prove2.me/submissions/bfa49bd8-a9aa-4549-9461-7d722285cbae

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_ReducedGame
import Definitions.Def_DataTrackComp_Surplus_AppendixC

set_option autoImplicit false

open DataTrackComp.Surplus Filter Topology

theorem solution :
    (∀ x m : ℝ, 0 < x → 0 < m → 0 < J2 x m) ∧
    (∀ x m : ℝ, 0 < m → 0 < x → x < xtilde m → Gam x m = J1 x m / J2 x m) ∧
    (∀ w z : ℝ, 0 < w → w < z →
      J1 (w ^ 2 / 2) (z ^ 2 - w ^ 2) = (w - z) * Q1 w z ∧ N (w ^ 2 / 2) (z ^ 2 - w ^ 2) = Q2 w z) := by
  have hJ2pos : ∀ x m : ℝ, 0 < x → 0 < m → 0 < J2 x m := by
    intro x m hx hm
    have hpos : 0 < 2 * x * (2 * x + m) := by positivity
    have hs0 := Real.sqrt_nonneg (2 * x * (2 * x + m))
    have hs2 := Real.sq_sqrt hpos.le
    have hlt : Real.sqrt (2 * x * (2 * x + m)) < 2 * m + 6 * x := by
      apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
      rw [hs2]
      nlinarith
    unfold J2
    have : 0 < 2 * m + 6 * x - Real.sqrt (2 * x * (2 * x + m)) := by linarith
    positivity
  refine ⟨hJ2pos, ?_, ?_⟩
  · intro x m hm hx hxt
    have hxle : x ≤ xtilde m := hxt.le
    have hpos : 0 < 2 * x * (2 * x + m) := by positivity
    have hg := (((hasDerivAt_id' x).const_mul 2).mul
      (((hasDerivAt_id' x).const_mul 2).add_const m)).congr_deriv (show _ = 8 * x + 2 * m by ring)
    have hsq := hg.sqrt hpos.ne'
    have hθd := ((((hasDerivAt_id' x).const_mul 2).add_const m).sub hsq).const_mul (1 / m)
    have hf := ((hasDerivAt_id' x).const_mul 2).mul hθd
    have heq : (fun y => psi y m) =ᶠ[𝓝 x]
        (fun y => 2 * y * (1 / m * (2 * y + m - Real.sqrt (2 * y * (2 * y + m))))) := by
      filter_upwards [eventually_lt_nhds hxt] with y hy
      simp only [psi, thetaBar, if_pos hy.le]
    have hderiv := (hf.congr_of_eventuallyEq heq).deriv
    have hθ : thetaBar x m = 1 / m * (2 * x + m - Real.sqrt (2 * x * (2 * x + m))) := by
      rw [thetaBar, if_pos hxle]
    have hpsi : psi x m = 2 * x * (1 / m * (2 * x + m - Real.sqrt (2 * x * (2 * x + m)))) := by
      rw [psi, hθ]
    have hZ : Z x m = psi x m / deriv (fun y => psi y m) x := by
      rw [Z, psix, if_neg hx.ne']
    rw [hderiv, hpsi] at hZ
    have hJ2 := hJ2pos x m hx hm
    rw [Gam, hZ, hθ, eq_div_iff hJ2.ne']
    unfold J1 J2 J3 J4
    have hs0 := Real.sqrt_pos.mpr hpos
    have hs2 := Real.sq_sqrt hpos.le
    simp only [Pi.sub_apply, Pi.mul_apply, mul_one] at *
    generalize hs : Real.sqrt (2 * x * (2 * x + m)) = s at *
    have hE : 0 < (4 * x + m) * s - 8 * x ^ 2 - 3 * m * x := by
      have hlt : (8 * x ^ 2 + 3 * m * x) ^ 2 < ((4 * x + m) * s) ^ 2 := by
        rw [mul_pow, hs2]
        have : 0 < x ^ 2 * (16 * m * x ^ 2 + 11 * m ^ 2 * x + 2 * m ^ 3) := by positivity
        nlinarith
      have := lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt
      linarith
    have hDE : (2 * (1 / m * (2 * x + m - s)) + 2 * x * (1 / m * (2 - (8 * x + 2 * m) / (2 * s)))) *
        (m * s) = 2 * ((4 * x + m) * s - 8 * x ^ 2 - 3 * m * x) := by
      field_simp
      linear_combination (-2) * hs2
    have hD : 2 * (1 / m * (2 * x + m - s)) + 2 * x * (1 / m * (2 - (8 * x + 2 * m) / (2 * s))) =
        2 * ((4 * x + m) * s - 8 * x ^ 2 - 3 * m * x) / (m * s) := by
      rw [eq_div_iff (by positivity)]
      exact hDE
    rw [hD]
    have hEne : (4 * x + m) * s - 8 * x ^ 2 - 3 * m * x ≠ 0 := hE.ne'
    have hEne' : s * (x * 4 + m) - x ^ 2 * 8 - m * x * 3 ≠ 0 := by
      intro h; apply hEne; linear_combination h
    have hEne'' : s * (x * 4 + m) - 8 * x ^ 2 - m * x * 3 ≠ 0 := by
      intro h; apply hEne; linear_combination h
    have hm0 : m ≠ 0 := hm.ne'
    have hs0' : s ≠ 0 := hs0.ne'
    field_simp
    linear_combination (-1152*x*(-2*m^2*s + 6*m^2*x - 6*m^2 + m*s^2 - 21*m*s*x + 2*m*s + 46*m*x^2 - 16*m*x + 4*s^2*x - 48*s*x^2 + 80*x^3)) * hs2
  · intro w z hw hwz
    have hz : 0 < z := hw.trans hwz
    have hsq : Real.sqrt (2 * (w ^ 2 / 2) * (2 * (w ^ 2 / 2) + (z ^ 2 - w ^ 2))) = w * z := by
      rw [show 2 * (w ^ 2 / 2) * (2 * (w ^ 2 / 2) + (z ^ 2 - w ^ 2)) = (w * z) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    constructor
    · rw [J1, hsq, J3, J4, Q1]
      ring
    · rw [N, hsq, Q2]
      ring
