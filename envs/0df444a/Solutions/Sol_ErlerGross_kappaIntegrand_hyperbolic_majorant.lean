-- Prove2me | solution 1 for ErlerGross.kappaIntegrand_hyperbolic_majorant
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T13:28:12.654454+00:00
-- url     : https://prove2.me/submissions/1aea1ece-8b07-4787-9434-089f4e0a129d

import Mathlib
import Definitions.Def_ErlerGross_defs

private lemma erlerGross_cosh_core (x : ℝ) (hx : 0 ≤ x) :
    2 * (Real.cosh x - 1) ≤ x * Real.sinh x := by
  let g : ℝ → ℝ := fun y => y * Real.cosh y - Real.sinh y
  let f : ℝ → ℝ := fun y => y * Real.sinh y - 2 * Real.cosh y + 2
  have hgderiv (y : ℝ) : deriv g y = y * Real.sinh y := by
    change deriv ((id * Real.cosh) - Real.sinh) y = _
    have hp : DifferentiableAt ℝ (id * Real.cosh) y :=
      differentiableAt_id.mul Real.differentiableAt_cosh
    rw [deriv_sub hp Real.differentiableAt_sinh]
    rw [deriv_mul differentiableAt_id Real.differentiableAt_cosh]
    simp [id, Real.deriv_cosh, Real.deriv_sinh]
  have hfderiv (y : ℝ) : deriv f y = g y := by
    change deriv (((id * Real.sinh) - ((fun _ : ℝ => 2) * Real.cosh)) + (fun _ => 2)) y = _
    have hp : DifferentiableAt ℝ (id * Real.sinh) y :=
      differentiableAt_id.mul Real.differentiableAt_sinh
    have hq : DifferentiableAt ℝ ((fun _ : ℝ => 2) * Real.cosh) y :=
      (differentiableAt_const (2 : ℝ)).mul Real.differentiableAt_cosh
    have hc : DifferentiableAt ℝ (fun _ : ℝ => (2 : ℝ)) y := differentiableAt_const 2
    rw [deriv_add (hp.sub hq) hc]
    rw [deriv_sub hp hq]
    rw [deriv_mul differentiableAt_id Real.differentiableAt_sinh]
    rw [deriv_mul (differentiableAt_const (2 : ℝ)) Real.differentiableAt_cosh]
    simp [id, g, Real.deriv_sinh, Real.deriv_cosh]
    ring
  have hzero : (0 : ℝ) ∈ Set.Icc 0 x := ⟨le_rfl, hx⟩
  have hgmono : MonotoneOn g (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · fun_prop
    · fun_prop
    · intro y hy
      rw [hgderiv]
      have hy' : 0 ≤ y := by
        have : y ∈ Set.Ioo (0 : ℝ) x := by simpa only [interior_Icc, Set.mem_Ioo] using hy
        exact le_of_lt this.1
      exact mul_nonneg hy' (Real.sinh_nonneg_iff.mpr hy')
  have hfmono : MonotoneOn f (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · fun_prop
    · fun_prop
    · intro y hy
      rw [hfderiv]
      have hy' : y ∈ Set.Icc (0 : ℝ) x := interior_subset hy
      have hh := hgmono hzero hy' hy'.1
      simpa [g] using hh
  have hfx := hfmono hzero ⟨hx, le_rfl⟩ hx
  have : 0 ≤ f x := by simpa [f] using hfx
  dsimp [f] at this
  linarith

theorem solution : forall kappa : Real, abs (ErlerGross.kappaIntegrand kappa) <=
      Real.pi / (8 * (1 + 2 * Real.cosh (Real.pi * kappa / 2)) ) := by
  intro kappa
  by_cases hk : kappa = 0
  · subst kappa
    simp [ErlerGross.kappaIntegrand]
    positivity
  · let x : ℝ := Real.pi * kappa / 2
    let a : ℝ := 1 + 2 * Real.cosh x
    let d : ℝ := 2 * abs kappa * Real.sinh (abs x)
    have hxne : x ≠ 0 := by
      dsimp [x]
      exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hk) (by norm_num)
    have hxa : abs x = Real.pi * abs kappa / 2 := by
      dsimp [x]
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hapos : 0 < a := by
      dsimp [a]
      linarith [Real.one_le_cosh x]
    have hnum : abs (1 - Real.cosh x) = Real.cosh x - 1 := by
      rw [abs_of_nonpos]
      · ring
      · linarith [Real.one_le_cosh x]
    have hden : abs (2 * kappa * Real.sinh x) = d := by
      dsimp [d]
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), Real.abs_sinh]
    have hdpos : 0 < d := by
      dsimp [d]
      exact mul_pos (mul_pos (by norm_num) (abs_pos.mpr hk))
        (Real.sinh_pos_iff.mpr (abs_pos.mpr hxne))
    have hcosh : Real.cosh x = Real.cosh (abs x) := by simp
    have hcore := erlerGross_cosh_core (abs x) (abs_nonneg x)
    have hratio : 8 * (Real.cosh x - 1) ≤ Real.pi * d := by
      rw [hcosh]
      calc
        8 * (Real.cosh (abs x) - 1) ≤ 4 * (abs x * Real.sinh (abs x)) := by nlinarith [hcore]
        _ = Real.pi * d := by rw [hxa]; dsimp [d]; rw [← hxa]; linear_combination 4 * Real.sinh (abs x) * hxa
    have hbase : (Real.cosh x - 1) / d ≤ Real.pi / 8 := by
      apply (div_le_iff₀ hdpos).2
      nlinarith [hratio]
    have hfactor :
        abs (ErlerGross.kappaIntegrand kappa) =
          ((Real.cosh x - 1) / d) / a := by
      dsimp [ErlerGross.kappaIntegrand]
      rw [abs_mul, abs_div, hnum, abs_of_pos hapos, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1), hden]
      dsimp [a, d, x]
      ring
    rw [hfactor]
    have := div_le_div_of_nonneg_right hbase (le_of_lt hapos)
    simpa [a, x, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
