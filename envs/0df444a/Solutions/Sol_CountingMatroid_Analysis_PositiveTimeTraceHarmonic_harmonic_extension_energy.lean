-- Prove2me | solution 1 for CountingMatroid.Analysis.PositiveTimeTraceHarmonic.harmonic_extension_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:05:18.127608+00:00
-- url     : https://prove2.me/submissions/e90ff8fe-bb96-4131-88f2-ffdc7e72e04a

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
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
section


set_option autoImplicit false

/-!
Harmonic extension for the concrete positive-time return subkernel. The
extension uses the increasing finite hitting kernels, so the first-step
identities do not assume almost-sure hitting from zero-weight states.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceHarmonic

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: Finite zero-time hitting entries increase with their horizon.
TEXLINE: main.tex:1047-1053 -/
theorem hitWithin_monotone (P : FinChain Ω) (A : Finset Ω) (x y : Ω) :
    Monotone (fun k => (hitWithin P A k).entry x y) :=
  monotone_nat_of_le_succ (fun k => hitWithin_succ_le P A k x y)

/-- INTERNAL: Hitting entries obey the same unit budget as the finite rows. -/
theorem hitWithin_bddAbove (P : FinChain Ω) (A : Finset Ω) (x y : Ω) :
    BddAbove (Set.range (fun k => (hitWithin P A k).entry x y)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact entry_le_one _ x y



/-- INTERNAL: Finite zero-time hitting converges to its uncapped entries. -/
theorem hitWithin_tendsto (P : FinChain Ω) (A : Finset Ω) (x y : Ω) :
    Filter.Tendsto (fun k => (hitWithin P A k).entry x y) Filter.atTop
      (nhds (uncappedHit P A x y)) :=
  tendsto_atTop_ciSup (hitWithin_monotone P A x y) (hitWithin_bddAbove P A x y)

/-- INTERNAL: The uncapped zero-time hit fixes every target state.
TEXLINE: main.tex:1047-1053 -/
theorem uncappedHit_on_target (P : FinChain Ω) (A : Finset Ω) (x y : Ω)
    (hx : x ∈ A) : uncappedHit P A x y = if x = y then 1 else 0 := by
  simp only [uncappedHit, hitWithin_on_target P A _ x y hx, ciSup_const]



/-- INTERNAL: Passing the finite return recursion to its monotone limit
identifies a positive return as one step followed by a zero-time hit.
TEXLINE: main.tex:1047-1055 -/
theorem uncappedReturn_first_step (P : FinChain Ω) (A : Finset Ω) (x y : Ω) :
    (uncappedReturn P A).entry x y = ∑ z, P x z * uncappedHit P A z y := by
  have hfinite (k : ℕ) : (returnWithin P A (k + 1)).entry x y =
      ∑ z, P x z * (hitWithin P A k).entry z y := rfl
  have hleft := (returnWithin_tendsto P A x y).comp (Filter.tendsto_add_atTop_nat 1)
  have hright := tendsto_finsetSum Finset.univ
    (fun z _ => (hitWithin_tendsto P A z y).const_mul (P x z))
  exact tendsto_nhds_unique hleft (by simpa only [Function.comp_def, hfinite] using hright)

/-- INTERNAL: The off-target first-step equation for uncapped zero-time hits.
TEXLINE: main.tex:1047-1055 -/
theorem uncappedHit_off_target (P : FinChain Ω) (A : Finset Ω) (x y : Ω)
    (hx : x ∉ A) : uncappedHit P A x y = (uncappedReturn P A).entry x y := by
  have hfinite (k : ℕ) : (hitWithin P A (k + 1)).entry x y =
      (returnWithin P A (k + 1)).entry x y := by
    simp only [hitWithin, hx, if_false, returnWithin]
  exact tendsto_nhds_unique
    ((hitWithin_tendsto P A x y).comp (Filter.tendsto_add_atTop_nat 1))
    (by simpa only [Function.comp_def, hfinite, uncappedReturn] using
      (returnWithin_tendsto P A x y).comp (Filter.tendsto_add_atTop_nat 1))



/-- INTERNAL: The extension retains its prescribed boundary values.
TEXLINE: main.tex:1047-1053 -/
theorem harmonicExtension_on_target (P : FinChain Ω) (A : Finset Ω)
    (h : Ω → ℝ) (x : Ω) (hx : x ∈ A) : harmonicExtension P A h x = h x := by
  simp [harmonicExtension, uncappedHit_on_target P A x _ hx]

/-- PAPER: main.tex:1051-1055
The residual of the harmonic extension vanishes off the target and equals
the positive-time trace residual on the target. -/
theorem harmonic_extension_residual (P : FinChain Ω) (A : Finset Ω)
    (h : Ω → ℝ) (x : Ω) :
    harmonicExtension P A h x - P.act (harmonicExtension P A h) x =
      if x ∈ A then h x - ∑ y, (uncappedReturn P A).entry x y * h y else 0 := by
  have hact : P.act (harmonicExtension P A h) x =
      ∑ y, (uncappedReturn P A).entry x y * h y := by
    simp only [FinKernel.act, harmonicExtension, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [uncappedReturn_first_step, Finset.sum_mul, mul_assoc]
  rw [hact]
  by_cases hx : x ∈ A
  · rw [if_pos hx, harmonicExtension_on_target P A h x hx]
  · rw [if_neg hx]
    simp only [harmonicExtension, uncappedHit_off_target P A x _ hx, sub_self]







end CountingMatroid.Analysis.PositiveTimeTraceHarmonic

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · monotone hitting limits give the harmonic residual and boundary energy identity; symmetry proves trace detailed balance, and one-step returns preserve holding probabilities. No almost-sure-hitting assumption on zero-weight states is needed.
-/

end
set_option autoImplicit false

/-!
Harmonic extension for the concrete positive-time return subkernel. The
extension uses the increasing finite hitting kernels, so the first-step
identities do not assume almost-sure hitting from zero-weight states.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceHarmonic
end CountingMatroid.Analysis.PositiveTimeTraceHarmonic
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PositiveTimeTraceHarmonic

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- PAPER: main.tex:1056-1063
Harmonic extension transfers the underlying Dirichlet form to the trace
boundary without requiring full support off the boundary. -/
theorem solution (μ : FinDist Ω) (P : FinChain Ω)
    (A : Finset Ω) (f g : Ω → ℝ) :
    dirichlet μ P (harmonicExtension P A f) (harmonicExtension P A g) =
      ∑ x ∈ A, μ x * f x *
        (g x - ∑ y, (uncappedReturn P A).entry x y * g y) := by
  unfold dirichlet ip
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ x, μ x * harmonicExtension P A f x *
        (harmonicExtension P A g x - P.act (harmonicExtension P A g) x) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ x, if x ∈ A then μ x * f x *
        (g x - ∑ y, (uncappedReturn P A).entry x y * g y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [harmonic_extension_residual]
      by_cases hx : x ∈ A
      · rw [if_pos hx, if_pos hx, harmonicExtension_on_target P A f x hx]
      · rw [if_neg hx, if_neg hx, mul_zero]
    _ = _ := by rw [← Finset.sum_filter]; simp
