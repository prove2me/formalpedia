-- Prove2me | solution 1 for AvramDividend.Classical.finiteGrid_ae_stoppedEvent_measure_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T14:01:31.351202+00:00
-- url     : https://prove2.me/submissions/2928725d-6926-4955-95e4-eedc4893ada9

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_finiteGrid_stoppedEvent_measure_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped BigOperators ENNReal

theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (τ : Ω → ι) (grid : Finset ι) (E : Set Ω)
    (hgrid : ∀ᵐ ω ∂μ, τ ω ∈ grid)
    (hcell : ∀ s ∈ grid, MeasurableSet (E ∩ {ω : Ω | τ ω = s})) :
    μ E = ∑ s ∈ grid, μ (E ∩ {ω : Ω | τ ω = s}) := by
  classical
  have hcover : ∀ᵐ ω ∂μ,
      (ω ∈ E ↔ ω ∈ ⋃ s ∈ grid, E ∩ {ω : Ω | τ ω = s}) := by
    filter_upwards [hgrid] with ω hw
    simp only [Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq, exists_prop]
    constructor
    · intro he
      exact ⟨τ ω, hw, he, rfl⟩
    · rintro ⟨s, -, he, -⟩
      exact he
  have hcoverEq : E =ᵐ[μ]
      (⋃ s ∈ grid, E ∩ {ω : Ω | τ ω = s}) := by
    filter_upwards [hcover] with ω hw
    exact propext hw
  calc
    μ E = μ (⋃ s ∈ grid, E ∩ {ω : Ω | τ ω = s}) :=
      measure_congr hcoverEq
    _ = ∑ s ∈ grid, μ (E ∩ {ω : Ω | τ ω = s}) := by
      rw [measure_biUnion_finset]
      · intro s _ s' _ hne
        refine Set.disjoint_left.2 fun ω h1 h2 => hne ?_
        exact h1.2.symm.trans h2.2
      · intro s hs
        exact hcell s hs
