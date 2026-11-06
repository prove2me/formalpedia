-- Prove2me | solution 1 for BianchiIX.entrance_radial_envelope
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:59:35.436382+00:00
-- url     : https://prove2.me/submissions/88caadd7-9353-4ee6-8d1e-d82452ae37dd

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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


theorem solution {k z u v w U V W : ℝ} (hk : 0 < k) (hz : 0 ≤ z)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hU0 : 0 ≤ U) (hW0 : 0 ≤ W)
    (hU : U ≤ u * Real.exp (-(1 + k / 3) * z))
    (hW : W ≤ w * Real.exp (-(1 + 1 / k) * z)) (hV : V = v * Real.exp z) :
    U * (V + W) + U ^ 2 + W ^ 2 / k ≤
      (u * (v + w) + u ^ 2) * Real.exp (-(k / 3) * z) +
        (w ^ 2 / k) * Real.exp (-2 * z) := by
  have hUs : U ≤ u * Real.exp (-(k / 3) * z) := hU.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [hz])) hu)
  have hUb : U ≤ u := hU.trans (mul_le_of_le_one_right hu
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hz)))
  have hWs : W ≤ w * Real.exp (-z) := hW.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (one_div_pos.mpr hk).le hz])) hw)
  have hWb : W ≤ w := hWs.trans (mul_le_of_le_one_right hw (Real.exp_le_one_iff.mpr (by linarith)))
  have hUV : U * V ≤ u * v * Real.exp (-(k / 3) * z) := by
    rw [hV]
    have H := mul_le_mul_of_nonneg_right hU (mul_nonneg hv (Real.exp_pos z).le)
    have heq : (u * Real.exp (-(1 + k / 3) * z)) * (v * Real.exp z) =
        u * v * Real.exp (-(k / 3) * z) := by
      calc
        _ = u * v * (Real.exp (-(1 + k / 3) * z) * Real.exp z) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
    exact H.trans_eq heq
  have hUW := mul_le_mul hUs hWb hW0 (mul_nonneg hu (Real.exp_pos _).le)
  have hU2 := mul_le_mul hUb hUs hU0 hu
  have hW2 := (sq_le_sq₀ hW0 (mul_nonneg hw (Real.exp_pos _).le)).mpr hWs
  have heq : (w * Real.exp (-z)) ^ 2 = w ^ 2 * Real.exp (-2 * z) := by
    rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
    congr 2
    ring
  rw [heq] at hW2
  have H := add_le_add (add_le_add hUV hUW) (add_le_add hU2 (div_le_div_of_nonneg_right hW2 hk.le))
  convert! H using 1 <;> ring
