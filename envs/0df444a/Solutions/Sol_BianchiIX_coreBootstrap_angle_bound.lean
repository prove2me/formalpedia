-- Prove2me | solution 1 for BianchiIX.coreBootstrap_angle_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:01:23.781482+00:00
-- url     : https://prove2.me/submissions/c9cf3438-419e-47fc-a40e-12f55b2d75cc

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cosh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.cosh (coreAngle m v) = coreRadius m v / v := by
  rw [coreAngle, Real.cosh_arsinh, coreAngle_sqrt hv]

end
end

theorem solution {k m v : ℝ} (hk : 6 ≤ k)
    (hr : coreRadius m v ≤ 101 / 100 * k) (hv : 1 ≤ v) :
    |coreAngle m v| ≤ Real.log (4 * k) := by
  have hv0 : 0 < v := by linarith
  have hc : Real.cosh (coreAngle m v) ≤ 101 / 100 * k := by
    rw [cosh_coreAngle hv0]
    exact (div_le_self (coreRadius_pos hv0).le hv).trans hr
  have he : Real.exp |coreAngle m v| ≤ 2 * Real.cosh (coreAngle m v) := by
    rw [← Real.cosh_abs (coreAngle m v), Real.cosh_eq]
    linarith [Real.exp_pos (-|coreAngle m v|)]
  apply (Real.le_log_iff_exp_le (by linarith : 0 < 4 * k)).mpr
  linarith
