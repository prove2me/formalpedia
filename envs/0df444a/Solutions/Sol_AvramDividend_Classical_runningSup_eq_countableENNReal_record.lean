-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_eq_countableENNReal_record
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T12:00:34.280879+00:00
-- url     : https://prove2.me/submissions/9656b800-cffc-4c92-b51b-cea00650ce02

import Theorems.Thm_AvramDividend_Classical_runningSup_eq_densePrefix_onSample
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_countable_bddRealSup_eq_ennrealOfRealSup_toReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A dense countable regulator record agrees with the actual regulator in its Borel ENNReal representation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (samples : ℕ → ℝ≥0)
    (hDense : Dense (Set.range samples))
    (hzero : (0 : ℝ≥0) ∈ Set.range samples)
    (t : ℝ≥0) (ht : t ∈ Set.range samples) :
    runningSup X t ω =
      (⨆ j : ℕ,
        ENNReal.ofReal (if samples j ≤ t then
          max 0 (X.X (samples j) ω) else 0)).toReal := by
  let S : Set ℝ≥0 := Set.range samples
  haveI : Nonempty {s : ℝ≥0 // s ∈ S ∧ s ≤ t} :=
    ⟨⟨t, ht, le_rfl⟩⟩
  let g : ℕ → ℝ := fun j =>
    if samples j ≤ t then max 0 (X.X (samples j) ω) else 0
  have hrecord : runningSup X t ω =
      ⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, X.X s.1 ω :=
    runningSup_eq_densePrefix_onSample X S hDense hzero t ht ω
  have hsub : BddAbove
      (Set.range (fun s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t} =>
        X.X s.1 ω)) := by
    obtain ⟨M, hM⟩ := levyPath_bddAbove_Icc X ω t
    refine ⟨M, ?_⟩
    rintro y ⟨s, rfl⟩
    exact hM ⟨s.1, ⟨(zero_le : (0 : ℝ≥0) ≤ s.1), s.2.2⟩, rfl⟩
  have hn : 0 ≤ runningSup X t ω := (runningSup_eq_rawSup_nonneg X t ω).2
  have hupper : ∀ j : ℕ, g j ≤ runningSup X t ω := by
    intro j
    dsimp [g]
    split_ifs with hj
    · apply max_le hn
      rw [hrecord]
      exact le_ciSup hsub ⟨samples j, ⟨j, rfl⟩, hj⟩
    · exact hn
  have hgBound : BddAbove (Set.range g) := by
    refine ⟨runningSup X t ω, ?_⟩
    rintro y ⟨j, rfl⟩
    exact hupper j
  have hgNonneg : 0 ≤ ⨆ j : ℕ, g j := by
    have h0g : 0 ≤ g 0 := by
      dsimp [g]
      split_ifs <;> simp
    exact h0g.trans (le_ciSup hgBound 0)
  have hlower : runningSup X t ω ≤ ⨆ j : ℕ, g j := by
    rw [hrecord]
    apply ciSup_le
    intro s
    obtain ⟨j, hj⟩ := s.2.1
    have hs : X.X s.1 ω ≤ g j := by
      dsimp [g]
      rw [hj]
      simp only [s.2.2, ↓reduceIte]
      exact le_max_right 0 (X.X s.1 ω)
    exact hs.trans (le_ciSup hgBound j)
  have hreal : runningSup X t ω = ⨆ j : ℕ, g j :=
    le_antisymm hlower (ciSup_le hupper)
  calc
    runningSup X t ω = ⨆ j : ℕ, g j := hreal
    _ = (⨆ j : ℕ, ENNReal.ofReal (g j)).toReal :=
      (countable_bddRealSup_eq_ennrealOfRealSup_toReal g hgBound hgNonneg).symm
    _ = _ := rfl
