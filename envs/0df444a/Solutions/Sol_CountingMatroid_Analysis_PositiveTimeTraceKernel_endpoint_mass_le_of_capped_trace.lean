-- Prove2me | solution 1 for CountingMatroid.Analysis.PositiveTimeTraceKernel.endpoint_mass_le_of_capped_trace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:10:43.058373+00:00
-- url     : https://prove2.me/submissions/9c35aad0-95ec-4b5e-82bf-4ebabcc970e3

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
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
Finite positive-time return kernels. Each row counts only returns completed
within the horizon; missing mass is retained as abort mass. The construction
uses the library's zero-time hitting recursion only after an initial transition,
so a starting transversal is not mistaken for an immediate return. Stationarity
also proves almost-sure return from positive-mass target states. This module
does not claim the spectral estimate or finite-bit operational coupling.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceKernel

open Arlib.Probability Arlib.MarkovChains

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]





































/-- INTERNAL: Capping loses mass pointwise relative to the uncapped return.
TEXLINE: main.tex:1207-1212 -/
theorem returnWithin_le_uncapped (P : FinChain Ω) (A : Finset Ω)
    (k : ℕ) (x y : Ω) :
    (returnWithin P A k).entry x y ≤ (uncappedReturn P A).entry x y :=
  le_ciSup (returnWithin_bddAbove P A x y) k

/-- INTERNAL: Composing pointwise dominated subkernels preserves domination.
TEXLINE: main.tex:1207-1212 -/
theorem compose_mono (K K' Q Q' : Subkernel Ω)
    (hK : ∀ x y, K.entry x y ≤ K'.entry x y)
    (hQ : ∀ x y, Q.entry x y ≤ Q'.entry x y) (x y : Ω) :
    (compose K Q).entry x y ≤ (compose K' Q').entry x y := by
  exact Finset.sum_le_sum fun z _ =>
    mul_le_mul (hK x z) (hQ z y) (Q.nonneg z y) (K'.nonneg x z)

/-- INTERNAL: The domination of capped by uncapped returns persists through
any number of trace transitions, retaining lost mass.
TEXLINE: main.tex:1163-1176,1207-1212 -/
theorem iterate_mono (K Q : Subkernel Ω)
    (h : ∀ x y, K.entry x y ≤ Q.entry x y) (k : ℕ) (x y : Ω) :
    (iterate K k).entry x y ≤ (iterate Q k).entry x y := by
  induction k generalizing x y with
  | zero => exact le_rfl
  | succ k ih => exact compose_mono K Q (iterate K k) (iterate Q k) h ih x y











end CountingMatroid.Analysis.PositiveTimeTraceKernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · built finite and uncapped positive-time return subkernels, their row budgets and cap domination; stationarity proves full return mass at positive-mass target states. The scheduled spectral estimate and finite-bit coupling belong to the consuming children.
-/


end
set_option autoImplicit false

/-!
Finite positive-time return kernels. Each row counts only returns completed
within the horizon; missing mass is retained as abort mass. The construction
uses the library's zero-time hitting recursion only after an initial transition,
so a starting transversal is not mistaken for an immediate return. Stationarity
also proves almost-sure return from positive-mass target states. This module
does not claim the spectral estimate or finite-bit operational coupling.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceKernel
end CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PositiveTimeTraceKernel

open Arlib.Probability Arlib.MarkovChains

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: Convert capped-to-uncapped comparison and an uncapped
pointwise mixing bound to an endpoint estimate from any subprobability start.
The support hypothesis restricts mixing to starts in the trace state space.
TEXLINE: main.tex:1219-1225,1242-1244 -/
theorem solution (P : FinChain Ω) (A : Finset Ω)
    (cap steps : ℕ) (ν : Ω → ℝ) (hν : ∀ x, 0 ≤ ν x)
    (hνmass : ∑ x, ν x ≤ 1) (hνsupport : ∀ x, x ∉ A → ν x = 0)
    (endpointMass bound : ℝ) (hbound : 0 ≤ bound) (y : Ω)
    (hoperational : endpointMass ≤
      ∑ x, ν x * (iterate (returnWithin P A cap) steps).entry x y)
    (hmixing : ∀ x ∈ A,
      (iterate (uncappedReturn P A) steps).entry x y ≤ bound) :
    endpointMass ≤ bound := by
  apply hoperational.trans
  calc
    (∑ x, ν x * (iterate (returnWithin P A cap) steps).entry x y) ≤
        ∑ x, ν x * bound := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x ∈ A
      · exact mul_le_mul_of_nonneg_left
          ((iterate_mono (returnWithin P A cap) (uncappedReturn P A)
            (returnWithin_le_uncapped P A cap) steps x y).trans (hmixing x hx)) (hν x)
      · rw [hνsupport x hx, zero_mul, zero_mul]
    _ ≤ bound := by
      rw [← Finset.sum_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hνmass hbound
