-- Prove2me | solution 1 for FunctionalInequalities.KLS.IsBorellDensity.ae_continuous_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:22:24.54796+00:00
-- url     : https://prove2.me/submissions/aea1fc41-35a3-4e88-84a2-944d6d5e92a5

import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set Topology Filter
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section Representative
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
variable [FiniteDimensional ℝ V]
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.IsBorellDensity
end FunctionalInequalities.KLS.IsBorellDensity
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.IsBorellDensity
namespace FunctionalInequalities.KLS.IsBorellDensity
end FunctionalInequalities.KLS.IsBorellDensity
open FunctionalInequalities.KLS.IsBorellDensity in
/-- A finite-dimensional Borell density is continuous Haar-almost everywhere.
It is continuous inside its convex positivity set, zero locally outside the
closure, and the frontier of that set has Haar measure zero. -/
theorem solution {ν m : Measure V} [m.IsAddHaarMeasure]
    {ρ : V → ℝ} (h : FunctionalInequalities.KLS.IsBorellDensity ν m ρ) :
    ∀ᵐ x ∂m, ContinuousAt ρ x := by
  let S : Set V := {x | 0 < ρ x}
  have hfront : m (frontier S) = 0 := h.convex_pos.addHaar_frontier m
  have hgood : ∀ᵐ x ∂m, x ∉ frontier S := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hfront
  filter_upwards [hgood] with x hx
  have hx' : x ∈ interior S ∪ interior Sᶜ := by
    exact (compl_frontier_eq_union_interior (s := S)) ▸ hx
  rcases hx' with hxS | hxSc
  · exact h.continuousOn_interior_pos.continuousAt (isOpen_interior.mem_nhds hxS)
  · have hnear : ρ =ᶠ[𝓝 x] (fun _ : V => (0 : ℝ)) := by
      filter_upwards [isOpen_interior.mem_nhds hxSc] with y hy
      have hnot : ¬ 0 < ρ y := interior_subset hy
      exact le_antisymm (le_of_not_gt hnot) (h.nonneg y)
    exact continuousAt_const.congr_of_eventuallyEq hnear
