-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_finset_cell_pair_exact_of_order_embedding
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:39:29.078161+00:00
-- url     : https://prove2.me/submissions/dd403b37-67bc-411f-987c-2a4117d8cbaa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_source_ordered_pairs_as_past_counts
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The exact source marked chronological pair count as an ordered-cell sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ)
    (F : Finset ℝ≥0) (hF : F = (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset)
    (k : ℕ) (g : ℝ≥0 → Fin k)
    (horder : ∀ u ∈ F, ∀ v ∈ F, (g u < g v) ↔ u < v) :
    (∑ i : Fin k,
      (F.filter (fun u => g u < i)).card *
      (F.filter (fun v => g v = i)).card) =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by
  classical
  have hpair :
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card =
        ∑ v ∈ F, (F.filter (fun u => u < v)).card := by
    simpa [hF] using
      (avram_p4_f_assembly_source_ordered_pairs_as_past_counts X ω T n)
  have hfilter (v : ℝ≥0) (hv : v ∈ F) :
      F.filter (fun u => g u < g v) = F.filter (fun u => u < v) := by
    ext u
    simp only [Finset.mem_filter]
    exact and_congr_right (fun hu => horder u hu v hv)
  calc
    (∑ i : Fin k, (F.filter (fun u => g u < i)).card *
        (F.filter (fun v => g v = i)).card) =
      ∑ i : Fin k, ∑ v ∈ F.filter (fun v => g v = i),
        (F.filter (fun u => g u < i)).card := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [mul_comm]
    _ = ∑ i : Fin k, ∑ v ∈ F,
          if g v = i then (F.filter (fun u => g u < i)).card else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_filter]
    _ = ∑ v ∈ F, ∑ i : Fin k,
          if g v = i then (F.filter (fun u => g u < i)).card else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ v ∈ F, (F.filter (fun u => g u < g v)).card := by
        apply Finset.sum_congr rfl
        intro v hv
        simp
    _ = ∑ v ∈ F, (F.filter (fun u => u < v)).card := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hfilter v hv]
    _ = ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card :=
      hpair.symm
