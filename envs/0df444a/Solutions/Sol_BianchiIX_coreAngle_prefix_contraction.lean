-- Prove2me | solution 1 for BianchiIX.coreAngle_prefix_contraction
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:05:43.801106+00:00
-- url     : https://prove2.me/submissions/c5e5afc6-633b-442e-9603-ed262930b670

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Theorems.Thm_BianchiIX_coreAngleField_product_nonpos
import Theorems.Thm_BianchiIX_coreAngleField_strong_le
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
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

noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.le_exp_of_linear_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hbound : ∀ u ∈ I, f' u ≤ c * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (t - s)) := by
  exact le_exp_of_clock_deriv_le hI hf (fun u _ => hasDerivAt_id u)
    (fun u hu => by simpa only [mul_one] using hbound u hu) hs ht hst

/-- Every completed bootstrap prefix has exponential strong-wall decay and decreasing VW. -/
theorem solution {I : Set ℝ} (hI : Convex ℝ I)
    {Y : ℝ → CoreAngleState} {k z₀ s t : ℝ} (hk : 6 ≤ k)
    (hY : ∀ z ∈ I, HasDerivAt Y (coreAngleField (z + z₀) (Y z)) z)
    (hr : ∀ z ∈ I, 99 / 100 * k ≤ Y z 0)
    (hv : ∀ z ∈ I, 1 ≤ Y z 0 / Real.cosh (z + z₀))
    (hu : ∀ z ∈ I, 0 ≤ Y z 1 ∧ Y z 1 ≤ (1 / 10000) / k)
    (hw : ∀ z ∈ I, 0 ≤ Y z 2 / (Y z 0 / Real.cosh (z + z₀)) ∧
      Y z 2 / (Y z 0 / Real.cosh (z + z₀)) ≤ (1 / 10000) / k)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    Y t 1 ≤ Y s 1 * Real.exp (-k * (t - s) / 4) ∧ Y t 2 ≤ Y s 2 := by
  constructor
  · have H := le_exp_of_linear_deriv_le hI (c := -k / 4)
      (fun z hz => hasDerivAt_pi.mp (hY z hz) 1)
      (fun z hz => coreAngleField_strong_le hk (hr z hz) (hu z hz) (hw z hz)) hs ht hst
    convert! H using 1
    congr 2
    ring
  · have hanti : AntitoneOn (fun z => Y z 2) I := antitoneOn_of_deriv_nonpos hI
      (fun z hz => (hasDerivAt_pi.mp (hY z hz) 2).continuousAt.continuousWithinAt)
      (fun z hz => (hasDerivAt_pi.mp (hY z (interior_subset hz)) 2).differentiableAt.differentiableWithinAt)
      (fun z hz => by
        rw [(hasDerivAt_pi.mp (hY z (interior_subset hz)) 2).deriv]
        exact coreAngleField_product_nonpos hk (hr z (interior_subset hz)) (hv z (interior_subset hz))
          (hu z (interior_subset hz)) (hw z (interior_subset hz)))
    exact hanti hs ht hst
