-- Prove2me | solution 1 for CountingMatroid.Analysis.CappedReturnSubstationary.hit_within_flow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:19:32.385982+00:00
-- url     : https://prove2.me/submissions/7a4f5d8a-933c-4430-8c22-4359b559584d

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
section


set_option autoImplicit false

/-!
Capped positive-time returns started from the stationary law restricted to
the target never put more mass on a target state than the stationary law
does. Iterating, any start dominated by a multiple of the restricted
stationary law stays dominated through every number of capped returns.
Lost (capped) mass is retained as a deficit, not renormalised.
-/
namespace CountingMatroid.Analysis.CappedReturnSubstationary

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]



/-- INTERNAL: Starting the flow one step later shifts its index. -/
theorem killed_flow_shift (P : FinChain Ω) (A : Finset Ω) (lam : Ω → ℝ) (s : ℕ) :
    killedFlow P A (killedFlow P A lam 1) s = killedFlow P A lam (s + 1) := by
  induction s with
  | zero => rfl
  | succ s ih =>
      funext w
      simp only [killedFlow] at ih ⊢
      rw [ih]









end CountingMatroid.Analysis.CappedReturnSubstationary

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · killed-flow decomposition of finite hitting, cumulative flow bound by stationarity, capped-return sub-stationarity and its iterated domination form.
-/

end
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

/-- INTERNAL: The mass hitting a target state within k steps is the total
flow arriving there at times 0,…,k.
TEXLINE: main.tex:1072-1087 -/
theorem solution (P : FinChain Ω) (A : Finset Ω) (k : ℕ) (lam : Ω → ℝ)
    (x : Ω) (hx : x ∈ A) :
    (∑ z, lam z * (hitWithin P A k).entry z x) =
      ∑ s ∈ Finset.range (k + 1), killedFlow P A lam s x := by
  induction k generalizing lam with
  | zero =>
      simp only [hitWithin, targetIdentity, zero_add, Finset.range_one,
        Finset.sum_singleton, killedFlow]
      rw [Finset.sum_eq_single x]
      · simp [hx]
      · intro z _ hz
        simp [hz]
      · simp
  | succ k ih =>
      have hsplit (z : Ω) : lam z * (hitWithin P A (k + 1)).entry z x =
          (if z = x then lam z else 0) +
            ∑ w, ((if z ∈ A then 0 else lam z) * P z w) *
              (hitWithin P A k).entry w x := by
        by_cases hz : z ∈ A
        · rw [hitWithin_on_target P A (k + 1) z x hz]
          by_cases hzx : z = x
          · subst hzx
            simp [hz]
          · simp [hz, hzx]
        · have hzx : z ≠ x := fun h => hz (h ▸ hx)
          simp only [hitWithin, hz, if_false, compose, ofChain, hzx, zero_add]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          ring
      simp_rw [hsplit, Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq' Finset.univ x, if_pos (Finset.mem_univ x)]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have hflow := ih (killedFlow P A lam 1)
      simp only [killedFlow] at hflow
      rw [hflow, Finset.sum_range_succ' _ (k + 1)]
      simp only [killedFlow]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      have h := killed_flow_shift P A lam s
      simp only [killedFlow] at h
      exact congrFun h x
