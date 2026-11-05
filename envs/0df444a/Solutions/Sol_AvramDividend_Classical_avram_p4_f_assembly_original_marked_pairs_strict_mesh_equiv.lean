-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_strict_mesh_equiv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:53:46.435882+00:00
-- url     : https://prove2.me/submissions/5a4192e9-9dc4-43f3-83ea-63f56a9e40a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pair_strict_mesh_index
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)) =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))) := by
  dsimp only
  obtain ⟨k, hk, horder⟩ :=
    avram_p4_f_assembly_original_marked_pair_strict_mesh_index X ω T hT n
  refine ⟨k, hk, ?_⟩
  ext p
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨ha, hb⟩, hab⟩
    exact ⟨⟨ha, hb⟩, horder p.1 ha p.2 hb hab⟩
  · rintro ⟨⟨ha, hb⟩, hab⟩
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · exact ⟨⟨ha, hb⟩, hlt⟩
    · simp [heq] at hab
    · have hreverse := horder p.2 hb p.1 ha hgt
      exact False.elim (lt_asymm hab hreverse)
