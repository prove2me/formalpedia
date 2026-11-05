-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_all_mesh_ceiling_pair_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:09:31.441497+00:00
-- url     : https://prove2.me/submissions/32e625dd-8edb-468d-9f98-14dc3c649565

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
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
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T) (n k : ℕ) (hk : 0 < k) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let g : ℝ≥0 → Fin (k + 1) := fun u =>
      ⟨min (Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))) k,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
    (∑ i : Fin (k + 1),
      (F.filter (fun u => g u < i)).card *
        (F.filter (fun v => g v = i)).card) =
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card := by
  classical
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let g : ℝ≥0 → Fin (k + 1) := fun u =>
    ⟨min (Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))) k,
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have hIdx : ∀ u ∈ F,
      0 < Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ∧
      Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ k := by
    exact avram_p4_f_assembly_original_marked_mesh_index_in_range X ω T hT n k hk
  have hg (u : ℝ≥0) (hu : u ∈ F) :
      (g u).val = Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) := by
    change min (Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))) k =
      Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))
    exact Nat.min_eq_left (hIdx u hu).2
  have hFilter :
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => g p.1 < g p.2)) =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨hu, hv⟩, hp⟩
      refine ⟨⟨hu, hv⟩, ?_⟩
      change (g p.1).val < (g p.2).val at hp
      simpa only [hg p.1 hu, hg p.2 hv] using hp
    · rintro ⟨⟨hu, hv⟩, hp⟩
      refine ⟨⟨hu, hv⟩, ?_⟩
      change (g p.1).val < (g p.2).val
      simpa only [hg p.1 hu, hg p.2 hv] using hp
  change (∑ i : Fin (k + 1),
      (F.filter (fun u => g u < i)).card *
        (F.filter (fun v => g v = i)).card) =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card
  rw [← hFilter]
  exact avram_p4_f_assembly_finite_grid_cross_pair_card_identity F (k + 1) g
