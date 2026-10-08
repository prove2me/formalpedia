-- Prove2me | solution 1 for AvramDividend.Classical.one_sided_limits_bddAbove_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T20:23:31.986985+00:00
-- url     : https://prove2.me/submissions/ae193494-2462-45cf-aa9c-a710f09486be

import Mathlib

open Set Filter Topology
open scoped NNReal ENNReal

theorem solution (f : ℝ≥0 → ℝ)
    (hr : ∀ t, Tendsto f (𝓝[≥] t) (𝓝 (f t)))
    (hl : ∀ t, ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l))
    (T : ℝ≥0) :
    BddAbove (Set.range (fun s : Set.Icc (0 : ℝ≥0) T => f s.1)) := by
  classical
  have hloc : ∀ t : ℝ≥0, ∃ s ∈ 𝓝 t,
      Bornology.IsBounded (f '' s) := by
    intro t
    obtain ⟨l, hlt⟩ := hl t
    obtain ⟨L, hL⟩ := hlt.isBoundedUnder_le.eventually_le
    obtain ⟨R, hR⟩ := (hr t).isBoundedUnder_le.eventually_le
    have hupper : ∀ᶠ v in 𝓝 t, f v ≤ max L R := by
      rw [← nhdsLT_sup_nhdsGE]
      exact eventually_sup.mpr
        ⟨hL.mono (fun v hv => le_trans hv (le_max_left _ _)),
         hR.mono (fun v hv => le_trans hv (le_max_right _ _))⟩
    obtain ⟨l', hlt'⟩ := hl t
    obtain ⟨L', hL'⟩ := hlt'.isBoundedUnder_ge.eventually_ge
    obtain ⟨R', hR'⟩ := (hr t).isBoundedUnder_ge.eventually_ge
    have hlower : ∀ᶠ v in 𝓝 t, min L' R' ≤ f v := by
      rw [← nhdsLT_sup_nhdsGE]
      exact eventually_sup.mpr
        ⟨hL'.mono (fun v hv => le_trans (min_le_left _ _) hv),
         hR'.mono (fun v hv => le_trans (min_le_right _ _) hv)⟩
    refine ⟨{v | min L' R' ≤ f v ∧ f v ≤ max L R},
      hlower.and hupper, ?_⟩
    have hBelow : BddBelow (f '' {v | min L' R' ≤ f v ∧
        f v ≤ max L R}) := by
      refine ⟨min L' R', ?_⟩
      rintro y ⟨v, hv, rfl⟩
      exact hv.1
    have hAbove : BddAbove (f '' {v | min L' R' ≤ f v ∧
        f v ≤ max L R}) := by
      refine ⟨max L R, ?_⟩
      rintro y ⟨v, hv, rfl⟩
      exact hv.2
    exact hBelow.isBounded hAbove
  have hcompact : IsCompact (Set.Icc (0 : ℝ≥0) T) := isCompact_Icc
  have himage : Bornology.IsBounded (f '' Set.Icc (0 : ℝ≥0) T) :=
    Bornology.isBounded_image_of_isLocallyBounded_of_isCompact
      hcompact hloc
  have hb : BddAbove (f '' Set.Icc (0 : ℝ≥0) T) := himage.bddAbove
  apply hb.mono
  rintro y ⟨s, rfl⟩
  exact ⟨s.1, s.2, rfl⟩
