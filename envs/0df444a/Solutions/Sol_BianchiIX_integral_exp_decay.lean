-- Prove2me | solution 1 for BianchiIX.integral_exp_decay
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:32:27.156258+00:00
-- url     : https://prove2.me/submissions/b04aa002-9651-43cb-a59d-8a3fd7f815a1

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


theorem solution {a b c : ℝ} (hc : 0 < c) :
    (∫ z in a..b, Real.exp (-c * (z - a))) = (1 - Real.exp (-c * (b - a))) / c := by
  have hd (z : ℝ) : HasDerivAt (fun u => -Real.exp (-c * (u - a)) / c)
      (Real.exp (-c * (z - a))) z := by
    convert! (((hasDerivAt_id z).sub_const a).const_mul (-c)).exp.neg.div_const c using 1
    simp only [id_eq]
    field_simp
  have hcont : Continuous (fun z => Real.exp (-c * (z - a))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hd z) (hcont.intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring
