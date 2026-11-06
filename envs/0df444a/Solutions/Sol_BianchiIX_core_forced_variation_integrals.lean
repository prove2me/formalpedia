-- Prove2me | solution 1 for BianchiIX.core_forced_variation_integrals
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:58:11.884064+00:00
-- url     : https://prove2.me/submissions/dde845ec-7256-4344-b8a3-83302a4a14d2

import Theorems.Thm_BianchiIX_integral_le_of_affine_exp_decay
import Theorems.Thm_BianchiIX_sech_le_exp
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

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory


/-- The two explicit integrals in (B.36), with no total-duration factor. -/
theorem solution {x : ℝ → ℝ} {k T z₀ U Q : ℝ}
    (hk : 6 ≤ k) (hT : 0 ≤ T) (hU : 0 ≤ U) (hQ : 0 ≤ Q)
    (hx : ContinuousOn x (Icc 0 T)) (hz₀ : Real.cosh z₀ = k)
    (hbound : ∀ t ∈ Icc 0 T,
      |x t| ≤ Real.exp (-k * t / 4) * (|x 0| + 3 * k * U * Q * t)) :
    (∫ t in 0..T, |x t| / Real.cosh (z₀ + t)) ≤ (12 * |x 0| + 432 * U * Q) / k ^ 2 ∧
      (∫ t in 0..T, |x t|) ≤ (4 * |x 0| + 48 * U * Q) / k := by
  have hk0 : 0 < k := by linarith only [hk]
  have hc : 0 < k / 4 := by positivity
  have hrate : k / 12 ≤ k / 4 - 1 := by linarith only [hk]
  have hrate0 : 0 < k / 4 - 1 := lt_of_lt_of_le (by positivity) hrate
  have hdecay (t : ℝ) (ht : t ∈ Icc 0 T) :
      |x t| ≤ Real.exp (-(k / 4) * (t - 0)) * (|x 0| + (3 * k * U * Q) * (t - 0)) := by
    convert! hbound t ht using 1
    congr 2 <;> ring
  constructor
  · have hweighted : ContinuousOn (fun t => |x t| / Real.cosh (z₀ + t)) (Icc 0 T) :=
      hx.abs.div (by fun_prop) (fun t _ => ne_of_gt (Real.cosh_pos _))
    have hpoint (t : ℝ) (ht : t ∈ Icc 0 T) :
        |x t| / Real.cosh (z₀ + t) ≤
          Real.exp (-(k / 4 - 1) * (t - 0)) * (|x 0| / k + (3 * U * Q) * (t - 0)) := by
      have hs := sech_le_exp (a := z₀) (b := z₀ + t) (by linarith only [ht.1])
      rw [hz₀, add_sub_cancel_left] at hs
      have H := mul_le_mul hs (hbound t ht) (abs_nonneg _) (by positivity : 0 ≤ (1 / k) * Real.exp t)
      calc
        _ = (1 / Real.cosh (z₀ + t)) * |x t| := by ring
        _ ≤ (1 / k * Real.exp t) * (Real.exp (-k * t / 4) * (|x 0| + 3 * k * U * Q * t)) := H
        _ = (Real.exp t * Real.exp (-k * t / 4)) * (|x 0| / k + 3 * U * Q * t) := by field_simp
        _ = _ := by
          rw [← Real.exp_add]
          congr 2 <;> ring
    have H := integral_le_of_affine_exp_decay hT hrate0 (div_nonneg (abs_nonneg _) hk0.le)
      (by positivity : 0 ≤ 3 * U * Q) hweighted hpoint
    have hrate2 := (sq_le_sq₀ (by positivity : 0 ≤ k / 12) hrate0.le).mpr hrate
    apply H.trans
    calc
      _ ≤ (|x 0| / k) / (k / 12) + (3 * U * Q) / (k / 12) ^ 2 := add_le_add
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hrate)
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hrate2)
      _ = _ := by field_simp; ring
  · have H := integral_le_of_affine_exp_decay hT hc (abs_nonneg (x 0))
      (by positivity : 0 ≤ 3 * k * U * Q) hx.abs hdecay
    convert! H using 1
    field_simp
    ring
