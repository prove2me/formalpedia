-- Prove2me | solution 1 for FunctionalInequalities.KLS.IsBorellDensity.ae_continuous_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:35:50.799962+00:00
-- url     : https://prove2.me/submissions/c3a2bb37-f243-4e0d-89e7-0b93e1ab363b

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic

noncomputable section
open MeasureTheory Set Topology Filter
section Representative
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
variable [FiniteDimensional ℝ V]
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
