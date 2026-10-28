-- Prove2me | solution 1 for CountingMatroid.Analysis.CappedReturnSubstationary.return_within_substationary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:41:09.765802+00:00
-- url     : https://prove2.me/submissions/6ac1ded9-19de-431a-bcc4-1f80c817bc15

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
import Theorems.Thm_CountingMatroid_Analysis_CappedReturnSubstationary_hit_within_flow
import Theorems.Thm_CountingMatroid_Analysis_CappedReturnSubstationary_killed_flow_le

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

/-- INTERNAL: Capped positive-time returns from the restricted stationary law
are sub-stationary on the target.
TEXLINE: main.tex:1072-1087,1226-1229 -/
theorem solution (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hμ : Stationary μ P) (k : ℕ) (x : Ω) :
    (∑ y, (if y ∈ A then μ y else 0) * (returnWithin P A k).entry y x) ≤
      if x ∈ A then μ x else 0 := by
  by_cases hx : x ∈ A
  · rw [if_pos hx]
    cases k with
    | zero =>
        simp only [returnWithin, mul_zero, Finset.sum_const_zero]
        exact μ.coe_nonneg x
    | succ k =>
        simp only [returnWithin, compose, ofChain]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp_rw [← mul_assoc, ← Finset.sum_mul]
        rw [hit_within_flow P A k _ x hx]
        exact killed_flow_le P A μ hμ k x
  · rw [if_neg hx]
    simp [returnWithin_supported P A k _ x hx]
