-- Prove2me | solution 1 for AvramDividend.Classical.continuousAt_eq_zero_of_ae_zero_at_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:03:56.768385+00:00
-- url     : https://prove2.me/submissions/548b93d1-47ad-4635-a5db-9c43c5c2a711

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (x : α)
    (hx : x ∈ μ.support)
    (hf : ContinuousAt f x)
    (hae : ∀ᵐ y ∂μ, f y = 0) :
    f x = 0 := by
  by_contra hne
  have hnhds : {y : α | f y ≠ 0} ∈ 𝓝 x := by
    have hh : {(0 : ℝ)}ᶜ ∈ 𝓝 (f x) :=
      isOpen_compl_singleton.mem_nhds (by simpa using hne)
    change f ⁻¹' ({(0 : ℝ)}ᶜ) ∈ 𝓝 x
    exact hf hh
  have hp : 0 < μ {y : α | f y ≠ 0} :=
    (Measure.mem_support_iff_forall x).mp hx _ hnhds
  have hz : μ {y : α | f y ≠ 0} = 0 := by
    simpa using (ae_iff.mp hae)
  exact (ne_of_gt hp) hz
