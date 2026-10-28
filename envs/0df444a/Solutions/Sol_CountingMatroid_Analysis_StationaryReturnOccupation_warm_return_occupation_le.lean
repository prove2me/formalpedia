-- Prove2me | solution 1 for CountingMatroid.Analysis.StationaryReturnOccupation.warm_return_occupation_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:41:30.637987+00:00
-- url     : https://prove2.me/submissions/d9c84117-6045-4bc6-9157-44421ce547c4

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Definitions.Def_CountingMatroid_Analysis_StationaryReturnOccupation
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
import Theorems.Thm_CountingMatroid_Analysis_StationaryReturnOccupation_stationary_return_occupation

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
Finite occupation bounds for positive-time returns. The first attempted step
is counted separately from the subsequent survival tails. Stationarity makes
the tails telescope, so neither irreducibility nor an infinite-expectation
interchange is needed. Operational finite-tape coupling is not asserted here.
-/
namespace CountingMatroid.Analysis.StationaryReturnOccupation
end CountingMatroid.Analysis.StationaryReturnOccupation
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.StationaryReturnOccupation

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: A U-warm positive-time return has finite occupation budget
at most U times any inverse-target-mass bound B. Missing operational mass
can be dominated by this budget without conditioning successful returns.
TEXLINE: main.tex:1072-1087,1226-1234 -/
theorem solution (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hstationary : Stationary μ P) (H : ℕ)
    (U B : ℝ) (hU : 0 ≤ U) (hmass : 0 < ∑ x ∈ A, μ x)
    (hB : 1 ≤ B * (∑ x ∈ A, μ x)) :
    U / (∑ x ∈ A, μ x) * returnOccupation P A μ H ≤ U * B := by
  have hocc : returnOccupation P A μ H ≤ 1 := by
    rw [stationary_return_occupation P A μ hstationary H]
    have hnonneg : 0 ≤ ∑ x, μ x * survive P A H x :=
      Finset.sum_nonneg fun x _ => mul_nonneg (μ.coe_nonneg x) (survive_nonneg P A H x)
    linarith
  calc
    U / (∑ x ∈ A, μ x) * returnOccupation P A μ H ≤
        U / (∑ x ∈ A, μ x) * 1 :=
      mul_le_mul_of_nonneg_left hocc (div_nonneg hU hmass.le)
    _ ≤ U * B := by
      rw [mul_one, div_le_iff₀ hmass]
      nlinarith [mul_le_mul_of_nonneg_left hB hU]
