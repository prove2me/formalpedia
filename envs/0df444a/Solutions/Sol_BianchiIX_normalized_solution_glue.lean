-- Prove2me | solution 1 for BianchiIX.normalized_solution_glue
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:38:48.97565+00:00
-- url     : https://prove2.me/submissions/7155baac-d187-48e5-9b4e-fefa7cebac6c

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Theorems.Thm_BianchiIX_normalized_solution_unique
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal


/-- Uniqueness makes the two solution germs agree on their whole overlap. -/
theorem solution {I J : Set ℝ}
    (hI : Convex ℝ I) (hoI : IsOpen I) (hJ : Convex ℝ J) (hoJ : IsOpen J)
    {α β : ℝ → NormalizedState}
    (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    (hβ : ∀ t ∈ J, HasDerivAt β (normalizedField (β t)) t)
    {s : ℝ} (hsI : s ∈ I) (hsJ : s ∈ J) (heq : α s = β s) :
    ∃ γ : ℝ → NormalizedState, EqOn γ α I ∧ EqOn γ β J ∧
      ∀ t ∈ I ∪ J, HasDerivAt γ (normalizedField (γ t)) t := by
  classical
  have hmatch := normalized_solution_unique (hI.inter hJ)
    (fun t ht => hα t ht.1) (fun t ht => hβ t ht.2) ⟨hsI, hsJ⟩ heq
  let γ : ℝ → NormalizedState := I.piecewise α β
  have heI : EqOn γ α I := fun t ht => piecewise_eq_of_mem I α β ht
  have heJ : EqOn γ β J := by
    intro t ht
    by_cases htI : t ∈ I
    · exact (heI htI).trans (hmatch ⟨htI, ht⟩)
    · exact piecewise_eq_of_notMem I α β htI
  refine ⟨γ, heI, heJ, fun t ht => ?_⟩
  rcases ht with ht | ht
  · rw [heI ht]
    exact (hα t ht).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hoI.mem_nhds ht) fun u hu => heI hu)
  · rw [heJ ht]
    exact (hβ t ht).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hoJ.mem_nhds ht) fun u hu => heJ hu)
