-- Prove2me | solution 1 for CountingMatroid.Analysis.CappedReturnSubstationary.iterate_return_substationary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:02:29.426797+00:00
-- url     : https://prove2.me/submissions/362a172f-34e9-4d06-8f3c-9514be92906b

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_CappedReturnSubstationary
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Order.MonotoneConvergence
import Theorems.Thm_CountingMatroid_Analysis_CappedReturnSubstationary_return_within_substationary

namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib
end Arlib
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
set_option autoImplicit false

/-!
Capped positive-time returns started from the stationary law restricted to
the target never put more mass on a target state than the stationary law
does. Iterating, any start dominated by a multiple of the restricted
stationary law stays dominated through every number of capped returns.
Lost (capped) mass is retained as a deficit, not renormalised.
-/
namespace CountingMatroid.Analysis.CappedReturnSubstationary
end CountingMatroid.Analysis.CappedReturnSubstationary
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CappedReturnSubstationary

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: A start dominated by a multiple of the restricted stationary
law stays so dominated through any number of capped returns.
TEXLINE: main.tex:1226-1229 -/
theorem solution (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hμ : Stationary μ P) (k : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (lam : Ω → ℝ) (hlam0 : ∀ y, 0 ≤ lam y)
    (hlam : ∀ y, lam y ≤ c * (if y ∈ A then μ y else 0)) (steps : ℕ) (x : Ω) :
    (∑ y, lam y * (iterate (returnWithin P A k) steps).entry y x) ≤
      c * (if x ∈ A then μ x else 0) := by
  induction steps generalizing lam with
  | zero =>
      simp only [iterate, identity]
      rw [Finset.sum_eq_single x]
      · simpa using hlam x
      · intro y _ hy
        simp [hy]
      · simp
  | succ steps ih =>
      simp only [iterate, compose]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      apply ih
      · intro z
        exact Finset.sum_nonneg fun y _ =>
          mul_nonneg (hlam0 y) ((returnWithin P A k).nonneg y z)
      · intro z
        calc
          (∑ y, lam y * (returnWithin P A k).entry y z) ≤
              ∑ y, (c * (if y ∈ A then μ y else 0)) * (returnWithin P A k).entry y z :=
            Finset.sum_le_sum fun y _ =>
              mul_le_mul_of_nonneg_right (hlam y) ((returnWithin P A k).nonneg y z)
          _ = c * ∑ y, (if y ∈ A then μ y else 0) * (returnWithin P A k).entry y z := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
          _ ≤ c * (if z ∈ A then μ z else 0) :=
            mul_le_mul_of_nonneg_left (return_within_substationary P A μ hμ k z) hc
