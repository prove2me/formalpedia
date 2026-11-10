-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus14_original_window_filter_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:54:37.904266+00:00
-- url     : https://prove2.me/submissions/dd56a474-301b-4343-9df5-bdeaad870b7a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original annulus count in a physical window is exactly the cardinal of
marked times selected from the finite original full-cutoff source set. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (n m : ℕ) (hnm : n ≤ m) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))) =
    (((avram_wave7_06_original_negative_band_marked_times_finite X ω T m).toFinset.filter
      (fun u => s < u ∧ u ≤ t ∧
        -(1 / ((n : ℝ) + 1)) <
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)).card : ℝ≥0∞) := by
  classical
  let Δ : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let c : ℝ := -(1 / ((n : ℝ) + 1))
  let d : ℝ := -(1 / ((m : ℝ) + 1))
  let F : Set ℝ≥0 := {u | 0 < u ∧ u ≤ T ∧ Δ u ≤ d}
  let S : Set ℝ≥0 := {u | 0 < u ∧ Δ u ≠ 0 ∧
    (u, Δ u) ∈ Ioc s t ×ˢ Ioc c d}
  have hF : F.Finite := by
    simpa only [F, Δ, d] using
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T m)
  have hSsub : S ⊆ F := by
    intro u hu
    rcases hu with ⟨_, _, hu⟩
    have hProd := Set.mem_prod.mp hu
    exact ⟨lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hProd.1.1,
      le_trans hProd.1.2 htT, hProd.2.2⟩
  have hS : S.Finite := hF.subset hSsub
  have hdNeg : d < 0 := by
    dsimp [d]
    have hden : 0 < (m : ℝ) + 1 := by positivity
    have hdiv : 0 < (1 : ℝ) / ((m : ℝ) + 1) := one_div_pos.mpr hden
    linarith
  have hFilter : hS.toFinset = hF.toFinset.filter
      (fun u => s < u ∧ u ≤ t ∧ c < Δ u) := by
    ext u
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
    constructor
    · intro hu
      have hs : u ∈ Ioc s t := (Set.mem_prod.mp hu.2.2).1
      have hm : Δ u ∈ Ioc c d := (Set.mem_prod.mp hu.2.2).2
      exact ⟨hSsub hu, hs.1, hs.2, hm.1⟩
    · rintro ⟨⟨hu0, huT, hud⟩, hus, hut, huc⟩
      refine ⟨lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hus,
        ne_of_lt (lt_of_le_of_lt hud hdNeg), ?_⟩
      exact Set.mem_prod.mpr ⟨⟨hus, hut⟩, ⟨huc, hud⟩⟩
  have hCount :=
    avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
      X ω (Ioc s t ×ˢ Ioc c d) (measurableSet_Ioc.prod measurableSet_Ioc)
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0}).map
      (fun u => (u, Δ u))) (Ioc s t ×ˢ Ioc c d) = (S.encard : ℝ≥0∞) at hCount
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0}).map
      (fun u => (u, Δ u))) (Ioc s t ×ˢ Ioc c d) =
      ((hF.toFinset.filter (fun u => s < u ∧ u ≤ t ∧ c < Δ u)).card : ℝ≥0∞)
  rw [hCount]
  rw [hS.encard_eq_coe]
  change ((S.ncard : ℝ≥0∞) =
    ((hF.toFinset.filter (fun u => s < u ∧ u ≤ t ∧ c < Δ u)).card : ℝ≥0∞))
  rw [Set.ncard_eq_toFinset_card S hS, hFilter]
