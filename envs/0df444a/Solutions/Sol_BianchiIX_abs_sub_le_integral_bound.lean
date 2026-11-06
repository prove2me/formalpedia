-- Prove2me | solution 1 for BianchiIX.abs_sub_le_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:33:30.683196+00:00
-- url     : https://prove2.me/submissions/ab26e26e-feda-43a5-b274-b9083de29c07

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


theorem solution {f f' B : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z) (hB : ContinuousOn B (Icc a b))
    (hbound : ∀ z ∈ Icc a b, |f' z| ≤ B z) :
    |f b - f a| ≤ ∫ z in a..b, B z := by
  apply (norm_sub_le_integral_of_norm_deriv_le_of_le hab
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hf z ⟨hz.1.le, hz.2.le⟩).differentiableAt.differentiableWithinAt)
    (ae_of_all _ fun z hz => ?_) (hB.intervalIntegrable_of_Icc hab))
  rw [(hf z ⟨hz.1.le, hz.2.le⟩).deriv, Real.norm_eq_abs]
  exact hbound z ⟨hz.1.le, hz.2.le⟩
