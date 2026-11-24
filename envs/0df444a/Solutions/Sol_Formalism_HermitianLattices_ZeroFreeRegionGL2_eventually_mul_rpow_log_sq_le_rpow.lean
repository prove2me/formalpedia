-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.eventually_mul_rpow_log_sq_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:17:00.453296+00:00
-- url     : https://prove2.me/submissions/ad236e2d-c6b1-4433-81b4-83871718e184

import Mathlib
open Filter Asymptotics Topology


theorem solution (ε M : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, M * (x ^ (ε / 5) * Real.log x ^ 2) ≤ x ^ ε := by
  let c : ℝ := 1 / (|M|+1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hz := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (show 0 < ε - ε/5 by linarith)).bound hc
  filter_upwards [hz,eventually_gt_atTop (1:ℝ)] with x hx hx1
  have hxp : 0 < x := by linarith
  have hh : Real.log x ^ (2:ℕ) ≤ c * x ^ (ε-ε/5) := by
    simpa [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log x)), abs_of_nonneg (Real.rpow_nonneg hxp.le _)] using hx
  have hc' : |M| * c ≤ 1 := by dsimp [c]; rw [← div_eq_mul_one_div]; apply (div_le_one (by positivity)).mpr; linarith
  have hpow := Real.rpow_nonneg hxp.le (ε/5)
  calc
    _ ≤ |M| * (x^(ε/5) * Real.log x^2) := mul_le_mul_of_nonneg_right (le_abs_self M) (mul_nonneg hpow (sq_nonneg _))
    _ ≤ |M| * (x^(ε/5) * (c * x^(ε-ε/5))) := by gcongr
    _ = (|M| * c) * x^ε := by rw [show |M| * (x^(ε/5) * (c * x^(ε-ε/5))) = (|M| * c)*(x^(ε/5)*x^(ε-ε/5)) by ring, ← Real.rpow_add hxp]; ring_nf
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hc' (Real.rpow_nonneg hxp.le ε)
