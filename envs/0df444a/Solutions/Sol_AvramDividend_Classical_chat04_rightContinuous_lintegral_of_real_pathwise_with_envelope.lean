-- Prove2me | solution 1 for AvramDividend.Classical.chat04_rightContinuous_lintegral_of_real_pathwise_with_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:00:42.349072+00:00
-- url     : https://prove2.me/submissions/36c67aa1-49ea-4cf6-b340-75c343fbe9db

import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LeftRightNhds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- A uniform integrable envelope lifts pathwise real right-continuity to
    right-continuity of its extended-nonnegative expectation. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (g : NNReal → Ω → ℝ) (t : NNReal) (envelope : Ω → ENNReal)
    (hpath : ∀ ω, ContinuousWithinAt (fun u => g u ω) (Ici t) t)
    (hmeas : ∀ᶠ u in 𝓝[Ici t] t,
      AEMeasurable (fun ω => ENNReal.ofReal (g u ω)) P)
    (hbound : ∀ᶠ u in 𝓝[Ici t] t,
      ∀ᵐ ω ∂P, ENNReal.ofReal (g u ω) ≤ envelope ω)
    (hfin : (∫⁻ ω, envelope ω ∂P) ≠ ⊤) :
    ContinuousWithinAt
      (fun u => ∫⁻ ω, ENNReal.ofReal (g u ω) ∂P)
      (Ici t) t := by
  have hlim : ∀ᵐ ω ∂P,
      Tendsto (fun u => ENNReal.ofReal (g u ω))
        (𝓝[Ici t] t) (𝓝 (ENNReal.ofReal (g t ω))) :=
    Filter.Eventually.of_forall fun ω =>
      (ENNReal.continuous_ofReal.tendsto _).comp (hpath ω).tendsto
  change Tendsto
    (fun u => ∫⁻ ω, ENNReal.ofReal (g u ω) ∂P)
    (𝓝[Ici t] t)
    (𝓝 (∫⁻ ω, ENNReal.ofReal (g t ω) ∂P))
  exact tendsto_lintegral_filter_of_dominated_convergence'
    envelope hmeas hbound hfin hlim
