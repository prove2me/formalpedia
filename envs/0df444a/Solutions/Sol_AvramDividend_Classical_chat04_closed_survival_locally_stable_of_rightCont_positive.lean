-- Prove2me | solution 1 for AvramDividend.Classical.chat04_closed_survival_locally_stable_of_rightCont_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:39:39.669024+00:00
-- url     : https://prove2.me/submissions/82b6e403-eb2c-4497-bcfa-92802b9799d3

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.LeftRightNhds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology

/-- If survival holds through a strictly positive right-continuous reserve, it
    persists through all sufficiently close later horizons. -/
theorem solution
    (f : NNReal → ℝ) (t : NNReal)
    (hfcont : ContinuousWithinAt f (Ici t) t)
    (htpos : 0 < f t)
    (htsurv : ∀ s : NNReal, s ≤ t → 0 ≤ f s) :
    ∀ᶠ u in 𝓝[Ici t] t, ∀ s : NNReal, s ≤ u → 0 ≤ f s := by
  have hmem : {u : NNReal | 0 < f u} ∈ 𝓝[Ici t] t := by
    exact hfcont.eventually (Ioi_mem_nhds htpos)
  obtain ⟨v, hv, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).mp hmem
  have hIco : Ico t v ∈ 𝓝[Ici t] t :=
    (mem_nhdsGE_iff_exists_Ico_subset).mpr ⟨v, hv, Subset.rfl⟩
  filter_upwards [hIco] with u hu s hsu
  by_cases hst : s ≤ t
  · exact htsurv s hst
  · have hts : t < s := lt_of_not_ge hst
    have hsIco : s ∈ Ico t v := ⟨hts.le, lt_of_le_of_lt hsu hu.2⟩
    exact (hsub hsIco).le
