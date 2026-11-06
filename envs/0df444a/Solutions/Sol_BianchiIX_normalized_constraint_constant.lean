-- Prove2me | solution 1 for BianchiIX.normalized_constraint_constant
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T14:01:03.734015+00:00
-- url     : https://prove2.me/submissions/c3e3db54-b452-400d-b35c-304d7f2add97

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Theorems.Thm_BianchiIX_hasDerivAt_stateConstraint
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

noncomputable section
open BianchiIX
open Set


theorem solution {I : Set ℝ} (hI : Convex ℝ I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    stateConstraint (α t) = stateConstraint (α t₀) := by
  have H := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hasDerivAt_stateConstraint (hα u hu)).hasDerivWithinAt)
    (C := 0) (fun _ _ => by simp) ht₀ ht
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using H
