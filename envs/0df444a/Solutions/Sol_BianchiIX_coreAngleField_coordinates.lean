-- Prove2me | solution 1 for BianchiIX.coreAngleField_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:27:57.918542+00:00
-- url     : https://prove2.me/submissions/d9b943c5-2a99-4664-b1b4-05a4d8d5ac35

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.tanh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.tanh (coreAngle m v) = (1 - m) / coreRadius m v := by
  rw [coreAngle, Real.tanh_arsinh, coreAngle_sqrt hv]
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_coordinates {m v : ℝ} (hv : 0 < v) :
    coreRadius m v / Real.cosh (coreAngle m v) = v ∧
      1 - coreRadius m v * Real.tanh (coreAngle m v) = m := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  rw [cosh_coreAngle hv, tanh_coreAngle hv]
  constructor
  · field_simp
  · field_simp
    ring

end
end

theorem solution {m u v w : ℝ} (hv : 0 < v) :
    coreAngleField (coreAngle m v) ![coreRadius m v, u, v * w] =
      ![(-coupling u v w + (m - 1) * (u - w) ^ 2 / coreRadius m v ^ 2) /
          coreClockFactor (coreRadius m v) u w,
        strongVelocity m u v w / (coreRadius m v * coreClockFactor (coreRadius m v) u w),
        -2 * (v * w) * (1 + coupling u v w) /
          (coreRadius m v * coreClockFactor (coreRadius m v) u w)] := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  have hv0 := ne_of_gt hv
  dsimp [coreAngleField]
  rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ hv0, tanh_coreAngle hv, cosh_coreAngle hv]
  ext i
  fin_cases i
  · dsimp
    congr 1
    field_simp
    ring
  · dsimp
    rw [← div_div (strongVelocity m u v w) (coreRadius m v) (coreClockFactor (coreRadius m v) u w)]
    congr 1
    field_simp
    rw [coreRadius_sq]
    unfold coreEnergy strongVelocity
    ring
  · rfl
