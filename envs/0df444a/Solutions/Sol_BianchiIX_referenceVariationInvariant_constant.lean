-- Prove2me | solution 1 for BianchiIX.referenceVariationInvariant_constant
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:03:56.918317+00:00
-- url     : https://prove2.me/submissions/d17ce0fd-5ee1-4a58-bb0d-1bbb10b01703

import Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
import Theorems.Thm_BianchiIX_hasDerivAt_referenceVariationInvariant
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
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
open Set


theorem solution {I : Set ℝ} (hI : Convex ℝ I)
    {k : ℝ} {xi : ℝ → ProjectiveState} {a : ℝ → ℝ}
    (hxi : ∀ t ∈ I, HasDerivAt xi (referenceVariationVelocity k t (xi t) (a t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    referenceVariationInvariant k t (xi t) = referenceVariationInvariant k s (xi s) := by
  have H := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hasDerivAt_referenceVariationInvariant (hxi u hu)).hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) hs ht
  simpa [sub_eq_zero] using H
