-- Prove2me | solution 1 for CountingMatroid.Analysis.CappedReturnSubstationary.killed_flow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:18:52.244484+00:00
-- url     : https://prove2.me/submissions/810ed2b7-c5d8-4c6a-bf94-ea78ffcb0061

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

/-- INTERNAL: Flow started from the one-step image of the restricted
stationary law never exceeds the stationary law, cumulatively in time.
TEXLINE: main.tex:1072-1087 -/
theorem solution (P : FinChain Ω) (A : Finset Ω) (μ : FinDist Ω)
    (hμ : Stationary μ P) (t : ℕ) (w : Ω) :
    (∑ s ∈ Finset.range (t + 1), killedFlow P A
      (fun w => ∑ z, (if z ∈ A then μ z else 0) * P z w) s w) ≤ μ w := by
  induction t generalizing w with
  | zero =>
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, killedFlow]
      rw [← hμ w]
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_right _ (P.coe_nonneg z w)
      split_ifs
      · exact le_rfl
      · exact μ.coe_nonneg z
  | succ t ih =>
      rw [Finset.sum_range_succ']
      simp only [killedFlow]
      have hswap : (∑ s ∈ Finset.range (t + 1), ∑ z, (if z ∈ A then 0 else
          killedFlow P A (fun w => ∑ z, (if z ∈ A then μ z else 0) * P z w) s z) *
            P z w) =
          ∑ z, (if z ∈ A then 0 else ∑ s ∈ Finset.range (t + 1),
            killedFlow P A (fun w => ∑ z, (if z ∈ A then μ z else 0) * P z w) s z) *
              P z w := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z _
        rw [← Finset.sum_mul]
        congr 1
        split_ifs <;> simp
      rw [hswap, ← Finset.sum_add_distrib, ← hμ w]
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : z ∈ A
      · simp [hz]
      · simp only [hz, if_false, zero_mul, add_zero]
        exact mul_le_mul_of_nonneg_right (ih z) (P.coe_nonneg z w)
