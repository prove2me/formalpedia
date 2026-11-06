-- Prove2me | solution 1 for BianchiIX.integral_clock_exp_decay
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:44:52.374718+00:00
-- url     : https://prove2.me/submissions/1df86a97-7a3b-4f86-ac77-e9883d477790

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
open Set MeasureTheory


theorem solution {z z' : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hzc : ContinuousOn z' (Icc a b)) :
    (∫ t in a..b, z' t * Real.exp (-c * (z t - z a))) =
      (1 - Real.exp (-c * (z b - z a))) / c := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => -Real.exp (-c * (z s - z a)) / c)
        (z' t * Real.exp (-c * (z t - z a))) t := by
    convert! (((hz t ht).sub_const (z a)).const_mul (-c)).exp.neg.div_const c using 1
    field_simp
  have hint : IntervalIntegrable (fun t => z' t * Real.exp (-c * (z t - z a))) volume a b :=
    (hzc.mul (Real.continuous_exp.comp_continuousOn
      (((HasDerivAt.continuousOn hz).sub continuousOn_const).const_mul (-c)))).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (uIcc_of_le hab ▸ ht)) hint]
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring
