-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_marked_grid_pair_count_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:05:45.865854+00:00
-- url     : https://prove2.me/submissions/3556e950-789c-45c2-9b55-8dde26d51de8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pair_strict_mesh_index
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_mesh_index_in_range
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_finite_grid_cross_pair_card_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧
      let g : ℝ≥0 → Fin (k + 1) := fun u =>
        ⟨min (Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))) k,
          Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
      (∑ i : Fin (k + 1),
        (F.filter (fun u => g u < i)).card *
          (F.filter (fun v => g v = i)).card) =
        ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by
  obtain ⟨k, hk, hstrict⟩ :=
    avram_p4_f_assembly_original_marked_pair_strict_mesh_index X ω T hT n
  refine ⟨k, hk, ?_⟩
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let g : ℝ≥0 → Fin (k + 1) := fun u =>
    ⟨min (Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))) k,
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have hg (u : ℝ≥0) (hu : u ∈ F) :
      (g u).val = Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) := by
    have hrange :=
      (avram_p4_f_assembly_original_marked_mesh_index_in_range
        X ω T hT n k hk) u hu
    simp [g, Nat.min_eq_left hrange.2]
  change (∑ i : Fin (k + 1),
    (F.filter (fun u => g u < i)).card *
      (F.filter (fun v => g v = i)).card) =
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
  rw [avram_p4_f_assembly_finite_grid_cross_pair_card_identity F (k + 1) g]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨ha, hb⟩, hidx⟩
    have hnat : Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)) := by
      simpa only [Fin.lt_def, hg p.1 ha, hg p.2 hb] using hidx
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · exact ⟨⟨ha, hb⟩, hlt⟩
    · simp [heq] at hnat
    · have hrev := hstrict p.2 hb p.1 ha hgt
      exact False.elim (lt_asymm hnat hrev)
  · rintro ⟨⟨ha, hb⟩, hlt⟩
    refine ⟨⟨ha, hb⟩, ?_⟩
    have hnat := hstrict p.1 ha p.2 hb hlt
    simpa only [Fin.lt_def, hg p.1 ha, hg p.2 hb] using hnat
