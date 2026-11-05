-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_gap_threshold_pair_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:34:09.779285+00:00
-- url     : https://prove2.me/submissions/733af45b-49d8-447f-ac38-ef086ccd8185

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_finite_band_grid_pair_exhaustion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ)
    (F : Finset ℝ≥0)
    (hF : F = (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset) :
    ∃ N, ∀ m ≥ N,
      (((F ×ˢ F).filter (fun p => p.1 < p.2)).filter
        (fun p => (1 : ℝ) / ((m : ℝ) + 1) <
          (p.2 : ℝ) - (p.1 : ℝ))) =
        (F ×ˢ F).filter (fun p => p.1 < p.2) := by
  classical
  let R : Finset (ℝ≥0 × ℝ≥0) :=
    (F ×ˢ F).filter (fun p => p.1 < p.2)
  let G : ℕ → Finset (ℝ≥0 × ℝ≥0) := fun m =>
    R.filter (fun p => (1 : ℝ) / ((m : ℝ) + 1) <
      (p.2 : ℝ) - (p.1 : ℝ))
  have hSub : ∀ m, G m ⊆ R := by
    intro m
    exact Finset.filter_subset _ _
  have hMono : Monotone G := by
    intro m k hmk p hp
    obtain ⟨hpR, hgap⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨hpR, ?_⟩
    have hh : ((m : ℝ) + 1) ≤ ((k : ℝ) + 1) := by
      exact_mod_cast Nat.add_le_add_right hmk 1
    have hfrac :
        (1 : ℝ) / ((k : ℝ) + 1) ≤
        (1 : ℝ) / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hh
    exact lt_of_le_of_lt hfrac hgap
  have hCover : ∀ p ∈ R, ∃ m, p ∈ G m := by
    intro p hp
    have hpLt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hrLt : (p.1 : ℝ) < (p.2 : ℝ) := by
      exact_mod_cast hpLt
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hrLt)
    exact ⟨m, Finset.mem_filter.mpr ⟨hp, hm⟩⟩
  have hStop :=
    avram_leanlevy_bridge_original_finite_band_grid_pair_exhaustion
      X ω T n F hF G hSub hMono hCover
  obtain ⟨N, hN⟩ := hStop
  refine ⟨(N : ℝ), ?_⟩
  intro m hm
  change R.filter (fun p => (1 : ℝ) / (m + 1) <
    (p.2 : ℝ) - (p.1 : ℝ)) = R
  apply Finset.Subset.antisymm
  · exact Finset.filter_subset _ _
  · intro p hp
    have hpN : p ∈ G N := by
      rw [hN N le_rfl]
      exact hp
    have hgap : (1 : ℝ) / ((N : ℝ) + 1) <
        (p.2 : ℝ) - (p.1 : ℝ) :=
      (Finset.mem_filter.mp hpN).2
    have hfrac :
        (1 : ℝ) / (m + 1) ≤
        (1 : ℝ) / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact Finset.mem_filter.mpr ⟨hp, lt_of_le_of_lt hfrac hgap⟩
