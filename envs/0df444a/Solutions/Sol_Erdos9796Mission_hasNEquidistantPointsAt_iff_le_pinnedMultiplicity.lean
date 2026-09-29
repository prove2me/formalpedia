-- Prove2me | solution 1 for Erdos9796Mission.hasNEquidistantPointsAt_iff_le_pinnedMultiplicity
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-11T16:43:45.239577+00:00
-- url     : https://prove2.me/submissions/49a8be80-821d-4431-94c4-c7f1ae14b6ba

import Definitions.Def_Erdos9796Mission_PinnedMultiplicity
import Theorems.Thm_Erdos9796Mission_mem_pinnedRadii_iff

open Erdos9796Mission

theorem solution
    {A : Finset Plane} {p : Plane} {n : ℕ} (hn : 0 < n) :
    HasNEquidistantPointsAt n A p ↔ n ≤ pinnedMultiplicity A p := by
  constructor
  · rintro ⟨r, hr, hcard⟩
    have hne : (A.filter (fun q => dist p q = r)).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨q, hq⟩ := hne
    rw [Finset.mem_filter] at hq
    have hmem : r ∈ pinnedRadii A p :=
      Erdos9796Mission.mem_pinnedRadii_iff.mpr ⟨⟨q, hq.1, hq.2⟩, hr⟩
    refine le_trans hcard ?_
    rw [pinnedMultiplicity]
    exact Finset.le_sup
      (f := fun r => (A.filter (fun q => dist p q = r)).card) hmem
  · intro h
    have hpos : 0 < pinnedMultiplicity A p := lt_of_lt_of_le hn h
    have hne : (pinnedRadii A p).Nonempty := by
      rcases Finset.eq_empty_or_nonempty (pinnedRadii A p) with hc | hc
      · rw [pinnedMultiplicity, hc, Finset.sup_empty] at hpos
        exact absurd hpos (lt_irrefl 0)
      · exact hc
    obtain ⟨r, hrmem, hreq⟩ :=
      Finset.exists_mem_eq_sup (pinnedRadii A p) hne
        (fun r => (A.filter (fun q => dist p q = r)).card)
    exact ⟨r, (Erdos9796Mission.mem_pinnedRadii_iff.mp hrmem).2, by
      rw [pinnedMultiplicity, hreq] at h
      exact h⟩
