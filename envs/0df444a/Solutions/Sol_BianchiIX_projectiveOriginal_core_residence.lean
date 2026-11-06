-- Prove2me | solution 1 for BianchiIX.projectiveOriginal_core_residence
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:09:45.719245+00:00
-- url     : https://prove2.me/submissions/0a412593-c9ac-4a27-8c09-fb81b1d686e9

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Theorems.Thm_BianchiIX_coreBootstrap_angle_bound
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_hasDerivAt_coreAngle_scaled
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
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


/-- A completed core segment has bounded duration in the original normalized time. -/
theorem solution {β : ℝ → ProjectiveState} {I : Set ℝ}
    {k s t : ℝ} (hk : 6 ≤ k) (hI : Convex ℝ I)
    (hβ : ∀ u ∈ I, HasDerivAt β (projectiveOriginalField (β u)) u)
    (hr : ∀ u ∈ I, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2) ∧
      coreRadius (β u 0) (β u 2) ≤ 101 / 100 * k)
    (hv : ∀ u ∈ I, 1 ≤ β u 2)
    (hu : ∀ u ∈ I, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k)
    (hw : ∀ u ∈ I, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    (t - s) / k ≤ coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2) ∧
      t - s ≤ 2 * k * Real.log (4 * k) := by
  let z := fun u => coreAngle (β u 0) (β u 2)
  let q := fun u => (6 / projectiveStateDenom (β u)) * coreRadius (β u 0) (β u 2) *
    coreClockFactor (coreRadius (β u 0) (β u 2)) (β u 1) (β u 3)
  have hz (u : ℝ) (hh : u ∈ I) : HasDerivAt z (q u) u :=
    hasDerivAt_coreAngle_scaled (hβ u hh) (lt_of_lt_of_le zero_lt_one (hv u hh))
  have hq (u : ℝ) (hh : u ∈ I) : 1 / k ≤ q u :=
    coreBootstrap_original_clock_lower hk (hr u hh) ((hv u hh).trans' zero_le_one) (hu u hh) (hw u hh)
  have H := hI.mul_sub_le_image_sub_of_le_deriv (HasDerivAt.continuousOn hz)
    (fun u hh => (hz u (interior_subset hh)).differentiableAt.differentiableWithinAt)
    (fun u hh => by rw [(hz u (interior_subset hh)).deriv]; exact hq u (interior_subset hh)) s hs t ht hst
  have H' : (t - s) / k ≤ z t - z s := by simpa only [one_div_mul_eq_div] using H
  refine ⟨H', ?_⟩
  have hzs := abs_le.mp (coreBootstrap_angle_bound hk (hr s hs).2 (hv s hs))
  have hzt := abs_le.mp (coreBootstrap_angle_bound hk (hr t ht).2 (hv t ht))
  have htime : (t - s) / k ≤ 2 * Real.log (4 * k) := by dsimp [z] at H'; linarith
  have H'' := (div_le_iff₀ (by linarith : 0 < k)).mp htime
  nlinarith
