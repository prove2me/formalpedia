-- Prove2me | solution 1 for CountingMatroid.Analysis.PositiveTimeTraceChain.trace_chain_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:36:47.430643+00:00
-- url     : https://prove2.me/submissions/93877e91-51c8-4246-a072-da1d98a21f79

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceChain
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceHarmonic
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
import Theorems.Thm_CountingMatroid_Analysis_PositiveTimeTraceHarmonic_harmonic_extension_energy

namespace Arlib
end Arlib
namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
set_option autoImplicit false

/-!
The concrete uncapped positive-time trace as a finite stochastic chain on its
boundary. Its law is the conditional underlying stationary law, and finite
powers agree with the previously constructed return subkernel iterates.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceChain
end CountingMatroid.Analysis.PositiveTimeTraceChain
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PositiveTimeTraceChain

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.PositiveTimeTraceHarmonic

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- PAPER: main.tex:1060-1063
Harmonic extension identifies trace Dirichlet energy with underlying energy
scaled by the probability mass of the boundary. -/
theorem solution (μ : FinDist Ω) (P : FinChain Ω)
    (hst : Stationary μ P) (A : Finset Ω) (hμ : ∀ x ∈ A, 0 < μ x)
    (hA : 0 < ∑ x ∈ A, μ x) (h : Ω → ℝ) :
    dirichlet μ P (harmonicExtension P A h) (harmonicExtension P A h) =
      (∑ x ∈ A, μ x) * dirichlet (traceLaw μ A hA)
        (traceChain μ P hst A hμ) (fun x => h x) (fun x => h x) := by
  rw [harmonic_extension_energy]
  have hact (x : A) : (traceChain μ P hst A hμ).act (fun y => h y) x =
      ∑ y, (uncappedReturn P A).entry x y * h y := by
    symm
    apply sum_on_target A
    intro y hy
    rw [uncappedReturn_supported P A x y hy, zero_mul]
  unfold dirichlet ip
  rw [← Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_subtype A (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro x _
  rw [hact]
  change μ x * h x * (h x - _) = (∑ z ∈ A, μ z) *
    ((μ x / (∑ z ∈ A, μ z)) * h x * h x -
      (μ x / (∑ z ∈ A, μ z)) * h x * _)
  field_simp
