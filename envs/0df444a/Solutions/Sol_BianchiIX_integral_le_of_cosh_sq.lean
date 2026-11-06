-- Prove2me | solution 1 for BianchiIX.integral_le_of_cosh_sq
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:36:15.57756+00:00
-- url     : https://prove2.me/submissions/81bb34fd-63f9-493a-8f98-e1af1a23532e

import Theorems.Thm_BianchiIX_integral_cosh_sq_le_endpoints
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


theorem solution {f : ℝ → ℝ} {a b B K : ℝ} (hab : a ≤ b)
    (hB : 0 ≤ B) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ z ∈ Icc a b, f z ≤ B * Real.cosh z ^ 2)
    (ha : Real.cosh a ≤ K) (hb : Real.cosh b ≤ K) :
    (∫ z in a..b, f z) ≤ 2 * B * K ^ 2 := by
  have hg : Continuous (fun z => B * Real.cosh z ^ 2) := by fun_prop
  have H := intervalIntegral.integral_mono_on (μ := volume) hab (hf.intervalIntegrable_of_Icc hab) (hg.intervalIntegrable _ _) hbound
  rw [intervalIntegral.integral_const_mul] at H
  have hsq : Real.cosh a ^ 2 + Real.cosh b ^ 2 ≤ 2 * K ^ 2 := by
    have ha' := (sq_le_sq₀ (Real.cosh_pos a).le ((Real.cosh_pos a).le.trans ha)).mpr ha
    have hb' := (sq_le_sq₀ (Real.cosh_pos b).le ((Real.cosh_pos b).le.trans hb)).mpr hb
    linarith
  exact H.trans ((mul_le_mul_of_nonneg_left ((integral_cosh_sq_le_endpoints hab).trans hsq) hB).trans_eq (by ring))
