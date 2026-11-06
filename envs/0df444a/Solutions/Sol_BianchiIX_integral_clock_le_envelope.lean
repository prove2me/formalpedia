-- Prove2me | solution 1 for BianchiIX.integral_clock_le_envelope
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:54:52.277394+00:00
-- url     : https://prove2.me/submissions/b545bc41-b59d-423d-9a96-ba0095986cf3

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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory


theorem solution {f z rate G : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hz : ∀ t ∈ Icc a b, HasDerivAt z (rate t) t)
    (hrate : ContinuousOn rate (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hf : ContinuousOn f (Icc a b)) (hG : Continuous G)
    (hbound : ∀ t ∈ Icc a b, f t ≤ G (z t)) :
    (∫ t in a..b, f t * rate t) ≤ ∫ s in z a..z b, G s := by
  have hzc : ContinuousOn z (Icc a b) := fun t ht => (hz t ht).continuousAt.continuousWithinAt
  have H := intervalIntegral.integral_mono_on (μ := volume) hab
    ((hf.mul hrate).intervalIntegrable_of_Icc hab)
    (((hG.comp_continuousOn hzc).mul hrate).intervalIntegrable_of_Icc hab)
    (fun t ht => mul_le_mul_of_nonneg_right (hbound t ht) (hpos t ht))
  have heq := intervalIntegral.integral_comp_mul_deriv
    (show ∀ t ∈ uIcc a b, HasDerivAt z (rate t) t by simpa only [uIcc_of_le hab] using hz)
    (show ContinuousOn rate (uIcc a b) by simpa only [uIcc_of_le hab] using hrate) hG
  simp only [Pi.mul_apply, Function.comp_apply] at H
  exact H.trans_eq (by simpa only [Function.comp_apply] using heq)
