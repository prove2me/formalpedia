-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_source_marked_cell_order_embedding
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:48:24.762425+00:00
-- url     : https://prove2.me/submissions/b45f3b2e-a1bd-4acd-a070-ead5dec67875

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pair_strict_mesh_index
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_mesh_index_in_range
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single finite uniform mesh embeds original negative-band marked-time order. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧ ∃ g : ℝ≥0 → Fin (k + 1),
      ∀ u ∈ F, ∀ v ∈ F, (g u < g v) ↔ u < v := by
  classical
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  obtain ⟨k, hk, hstrict⟩ :=
    avram_p4_f_assembly_original_marked_pair_strict_mesh_index X ω T hT n
  let ind (u : ℝ≥0) := Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))
  have hbound (u : ℝ≥0) (hu : u ∈ F) : ind u < k + 1 := by
    exact Nat.lt_succ_of_le
      ((avram_p4_f_assembly_original_marked_mesh_index_in_range
        X ω T hT n k hk u hu).2)
  let g : ℝ≥0 → Fin (k + 1) := fun u =>
    if hu : u ∈ F then ⟨ind u, hbound u hu⟩
    else ⟨0, Nat.zero_lt_succ k⟩
  change ∃ k : ℕ, 0 < k ∧ ∃ g : ℝ≥0 → Fin (k + 1),
    ∀ u ∈ F, ∀ v ∈ F, (g u < g v) ↔ u < v
  refine ⟨k, hk, g, ?_⟩
  intro u hu v hv
  have hgu : (g u).val = ind u := by simp [g, hu]
  have hgv : (g v).val = ind v := by simp [g, hv]
  constructor
  · intro h
    change (g u).val < (g v).val at h
    have hnat : ind u < ind v := by simpa only [hgu, hgv] using h
    by_contra hnot
    have hle : v ≤ u := le_of_not_gt hnot
    rcases eq_or_lt_of_le hle with heq | hvu
    · subst v
      exact (lt_irrefl _ hnat)
    · have hrev : ind v < ind u := by
        exact hstrict v hv u hu hvu
      exact (lt_asymm hnat hrev)
  · intro huv
    change (g u).val < (g v).val
    rw [hgu, hgv]
    exact hstrict u hu v hv huv
