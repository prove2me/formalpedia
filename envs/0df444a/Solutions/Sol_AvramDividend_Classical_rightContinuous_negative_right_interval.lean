-- Prove2me | solution 1 for AvramDividend.Classical.rightContinuous_negative_right_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:30:11.13323+00:00
-- url     : https://prove2.me/submissions/938bad8f-922f-4575-a8dc-5adb330693cc

import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped NNReal

theorem solution
    (f : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hcont : ContinuousWithinAt f (Ici t) t)
    (hneg : f t < 0) :
    ∃ u : ℝ≥0, t < u ∧
      ∀ s : ℝ≥0, t ≤ s → s < u → f s < 0 := by
  have hsmall : ∀ᶠ s in 𝓝[Ici t] t, f s < 0 :=
    hcont.eventually (isOpen_Iio.mem_nhds hneg)
  have hfull : ∀ᶠ s in 𝓝 t, s ∈ Ici t → f s < 0 :=
    eventually_nhdsWithin_iff.mp hsmall
  have hAbove : ∃ v : ℝ≥0, t < v := by
    refine ⟨t + 1, ?_⟩
    exact lt_add_of_pos_right t (zero_lt_one : (0 : ℝ≥0) < 1)
  obtain ⟨u, htu, hu⟩ :=
    exists_Ico_subset_of_mem_nhds hfull hAbove
  refine ⟨u, htu, ?_⟩
  intro s hle hlt
  exact (hu ⟨hle, hlt⟩) hle
