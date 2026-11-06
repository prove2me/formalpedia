-- Prove2me | solution 1 for BianchiIX.referenceClock_normalized_orbit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:45:44.075815+00:00
-- url     : https://prove2.me/submissions/1c5f970a-7fd4-43c8-bbcb-abe47ea5602d

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Definitions.Def_BianchiIX_Dynamics_ReferenceActualVariation
import Theorems.Thm_BianchiIX_exists_projective_normalized_reparametrization
import Theorems.Thm_BianchiIX_hasDerivAt_referencePulse
import Theorems.Thm_BianchiIX_referencePulse_clock_integral
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff

noncomputable section
open BianchiIX
open Set


theorem solution (k t : ℝ) :
    referenceClock k t ∈ normalizedMaxDomain (referenceEntryState k) 0 ∧
    normalizedMaxCurve (referenceEntryState k) 0 (referenceClock k t) =
      fromProjectiveState (referencePulse k t) := by
  obtain ⟨e, hsrc, he, _, _, _, _, _, hdom, hflow⟩ :=
    exists_projective_normalized_reparametrization (β := referencePulse k)
      (s := -referenceHalfTime k) convex_univ isOpen_univ (mem_univ _)
      (fun u _ => hasDerivAt_referencePulse k u) (fun u _ => referencePulse_denom_pos k u)
  have hmem : t ∈ e.source := by rw [hsrc]; trivial
  have ht : e t = referenceClock k t := by rw [he, referencePulse_clock_integral]; rfl
  have htarget : referenceClock k t ∈ e.target := ht ▸ e.map_source hmem
  have hinv : e.symm (referenceClock k t) = t := by rw [← ht, e.left_inv hmem]
  refine ⟨hdom htarget, ?_⟩
  have H := (hflow _ htarget).1
  rw [hinv] at H
  exact H.symm
