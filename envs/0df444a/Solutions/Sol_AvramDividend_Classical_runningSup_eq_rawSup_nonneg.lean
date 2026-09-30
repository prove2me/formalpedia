-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_eq_rawSup_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T16:48:10.095782+00:00
-- url     : https://prove2.me/submissions/7b894f46-883b-4ab6-b2bc-c279df427c50

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection

open MeasureTheory Filter Set Topology Bornology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω) :
    (runningSup X t ω = ⨆ s : Set.Icc (0 : ℝ≥0) t, X.X s.1 ω) ∧
      0 ≤ runningSup X t ω := by
  let f : ℝ≥0 → ℝ := fun y => X.X y ω
  let g : Set.Icc (0 : ℝ≥0) t → ℝ := fun s => f s.1
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
  let z : Set.Icc (0 : ℝ≥0) t := ⟨0, by simp⟩
  letI : Nonempty (Set.Icc (0 : ℝ≥0) t) := ⟨z⟩
  have hz : g z = 0 := by
    simpa [g, f, z] using X.X_zero ω
  have hnonneg : 0 ≤ ⨆ s, g s := by
    rw [← hz]
    exact le_ciSup hf z
  have hmax : BddAbove (Set.range fun s => max (g s) 0) := by
    obtain ⟨M, hM⟩ := hf
    refine ⟨max M 0, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact max_le_max (hM (Set.mem_range_self s)) le_rfl
  have hsup : (⨆ s, max (g s) 0) = ⨆ s, g s := by
    apply le_antisymm
    · apply ciSup_le
      intro s
      exact max_le (le_ciSup hf s) hnonneg
    · exact ciSup_mono hmax (fun s => le_max_left _ _)
  have heq :
      runningSup X t ω = ⨆ s : Set.Icc (0 : ℝ≥0) t, X.X s.1 ω := by
    simpa [runningSup, maxZero, g, f] using hsup
  exact ⟨heq, by rw [heq]; simpa [g, f] using hnonneg⟩
