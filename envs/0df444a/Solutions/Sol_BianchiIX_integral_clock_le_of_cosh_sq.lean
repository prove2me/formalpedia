-- Prove2me | solution 1 for BianchiIX.integral_clock_le_of_cosh_sq
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:30:18.683063+00:00
-- url     : https://prove2.me/submissions/656049d4-1754-4664-a77f-57a477cdf1c7

import Theorems.Thm_BianchiIX_integral_clock_le_envelope
import Theorems.Thm_BianchiIX_integral_le_of_cosh_sq
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


theorem solution {f z rate : ℝ → ℝ} {a b B K : ℝ}
    (hab : a ≤ b) (hz : ∀ t ∈ Icc a b, HasDerivAt z (rate t) t)
    (hrate : ContinuousOn rate (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hB : 0 ≤ B) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f t ≤ B * Real.cosh (z t) ^ 2)
    (ha : Real.cosh (z a) ≤ K) (hb : Real.cosh (z b) ≤ K) :
    (∫ t in a..b, f t * rate t) ≤ 2 * B * K ^ 2 := by
  have hzc : ContinuousOn z (Icc a b) := fun t ht => (hz t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn z (Icc a b) := monotoneOn_of_deriv_nonneg (convex_Icc a b) hzc
    (fun t ht => (hz t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hz t (interior_subset ht)).deriv]; exact hpos t (interior_subset ht))
  have hzab := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hG : Continuous (fun s => B * Real.cosh s ^ 2) := by fun_prop
  exact (integral_clock_le_envelope hab hz hrate hpos hf hG hbound).trans
    (integral_le_of_cosh_sq hzab hB hG.continuousOn (fun _ _ => le_rfl) ha hb)
