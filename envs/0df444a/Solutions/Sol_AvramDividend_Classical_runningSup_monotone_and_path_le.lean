-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_monotone_and_path_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:18:08.544085+00:00
-- url     : https://prove2.me/submissions/9a0c43fc-5d7c-4bb8-8c31-ce6be5f31823

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.MetricSpace.Bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology Bornology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Monotone (fun t : ℝ≥0 => runningSup X t ω) ∧
    ∀ t : ℝ≥0, X.X t ω ≤ runningSup X t ω := by
  let f : ℝ≥0 → ℝ := fun y => X.X y ω
  have hlocal : ∀ x : ℝ≥0, ∃ U ∈ 𝓝 x, IsBounded (f '' U) := by
    intro x
    by_cases hx : x = 0
    · subst x
      have hrc : Tendsto f (𝓝 0) (𝓝 (f 0)) := by
        simpa [f, Set.Ici_zero_eq_univ] using (X.rightCont ω 0).tendsto
      exact Metric.exists_isBounded_image_of_tendsto hrc
    · have hxpos : 0 < x := pos_iff_ne_zero.mpr hx
      obtain ⟨l, hl⟩ := X.leftLim ω x hxpos
      obtain ⟨-, ⟨⟨A, ⟨hA, ⟨W, hW, rfl⟩⟩⟩, hAW⟩⟩ :=
        Metric.exists_isBounded_image_of_tendsto hl
      obtain ⟨-, ⟨⟨B, ⟨hB, ⟨R, hR, rfl⟩⟩⟩, hBR⟩⟩ :=
        Metric.exists_isBounded_image_of_tendsto (X.rightCont ω x).tendsto
      refine ⟨A ∩ B, inter_mem hA hB, ?_⟩
      apply (hAW.union hBR).subset
      rintro _ ⟨y, ⟨hyA, hyB⟩, rfl⟩
      by_cases hyx : y < x
      · exact Set.mem_union_left _ ⟨y, ⟨hyA, hW hyx⟩, rfl⟩
      · exact Set.mem_union_right _ ⟨y, ⟨hyB, hR (le_of_not_gt hyx)⟩, rfl⟩
  have hBdd (t : ℝ≥0) :
      BddAbove (Set.range
        (fun s : Set.Icc (0 : ℝ≥0) t => maxZero (X.X s.1 ω))) := by
    let g : Set.Icc (0 : ℝ≥0) t → ℝ := fun s => f s.1
    have hcompact : IsBounded (f '' Set.Icc 0 t) :=
      isBounded_image_of_isLocallyBounded_of_isCompact isCompact_Icc hlocal
    have hrange : Set.range g = f '' Set.Icc 0 t := by
      ext z
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨s.1, s.2, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, hs⟩, rfl⟩
    have hf : BddAbove (Set.range g) := by
      rw [hrange]
      exact hcompact.bddAbove
    obtain ⟨M, hM⟩ := hf
    refine ⟨max M 0, ?_⟩
    rintro _ ⟨s, rfl⟩
    simpa [maxZero, g, f] using
      (max_le_max (hM (Set.mem_range_self s)) le_rfl)
  constructor
  · intro s t hst
    letI : Nonempty (Set.Icc (0 : ℝ≥0) s) := ⟨⟨0, by simp⟩⟩
    letI : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨⟨0, by simp⟩⟩
    change (⨆ r : Set.Icc (0 : ℝ≥0) s, maxZero (X.X r.1 ω)) ≤
      (⨆ r : Set.Icc (0 : ℝ≥0) t, maxZero (X.X r.1 ω))
    apply ciSup_le
    intro r
    let rt : Set.Icc (0 : ℝ≥0) t :=
      ⟨r.1, ⟨r.2.1, le_trans r.2.2 hst⟩⟩
    exact le_ciSup (hBdd t) rt
  · intro t
    letI : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨⟨0, by simp⟩⟩
    change X.X t ω ≤
      (⨆ r : Set.Icc (0 : ℝ≥0) t, maxZero (X.X r.1 ω))
    let r : Set.Icc (0 : ℝ≥0) t := ⟨t, by simp⟩
    have hx : X.X t ω ≤ maxZero (X.X r.1 ω) :=
      le_max_left _ _
    exact hx.trans (le_ciSup (hBdd t) r)
