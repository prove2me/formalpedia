-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_ceil_grid_past_cell_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:26:46.622193+00:00
-- url     : https://prove2.me/submissions/b95bb2d7-9c1b-4f58-b130-0c82c8a2574c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_mesh_index_in_range
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_all_mesh_ceiling_pair_card
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
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) < Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card =
    ∑ i : Fin k,
      (F.filter (fun (u : ℝ≥0) => Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i.val)).card *
      (F.filter (fun (v : ℝ≥0) => Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) = i.val + 1)).card := by
  classical
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let g : ℝ≥0 → Fin (k + 1) := fun u =>
    ⟨min (Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))) k,
      Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have hIdx : ∀ u ∈ F,
      0 < Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ∧ Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ k := by
    exact avram_p4_f_assembly_original_marked_mesh_index_in_range X ω T hT n k hk
  have hg (u : ℝ≥0) (hu : u ∈ F) :
      (g u).val = Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) := by
    change min (Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))) k = Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))
    exact Nat.min_eq_left (hIdx u hu).2
  have hPast (i : Fin k) :
      F.filter (fun (u : ℝ≥0) => g u < i.succ) =
      F.filter (fun (u : ℝ≥0) => Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i.val) := by
    ext u
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hu, hlt⟩
      refine ⟨hu, ?_⟩
      change (g u).val < (i.succ).val at hlt
      simpa [hg u hu, Nat.lt_succ_iff] using hlt
    · rintro ⟨hu, hle⟩
      refine ⟨hu, ?_⟩
      change (g u).val < (i.succ).val
      simpa [hg u hu, Nat.lt_succ_iff] using hle
  have hCell (i : Fin k) :
      F.filter (fun (v : ℝ≥0) => g v = i.succ) =
      F.filter (fun (v : ℝ≥0) => Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) = i.val + 1) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, heq⟩
      refine ⟨hv, ?_⟩
      have hval := congrArg Fin.val heq
      simpa [hg v hv] using hval
    · rintro ⟨hv, heq⟩
      refine ⟨hv, ?_⟩
      apply Fin.ext
      simpa [hg v hv] using heq
  have hAll :
      (∑ i : Fin (k + 1),
        (F.filter (fun (u : ℝ≥0) => g u < i)).card *
          (F.filter (fun (v : ℝ≥0) => g v = i)).card) =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) < Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card := by
    exact avram_leanlevy_bridge_original_all_mesh_ceiling_pair_card
      X ω T hT n k hk
  rw [Fin.sum_univ_succ] at hAll
  simp only [Fin.not_lt_zero, Finset.filter_false, Finset.card_empty,
    zero_mul, zero_add] at hAll
  have hSum :
      (∑ i : Fin k,
        (F.filter (fun (u : ℝ≥0) => g u < i.succ)).card *
          (F.filter (fun (v : ℝ≥0) => g v = i.succ)).card) =
      ∑ i : Fin k,
        (F.filter (fun (u : ℝ≥0) => Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i.val)).card *
          (F.filter (fun (v : ℝ≥0) => Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) = i.val + 1)).card := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hPast i, hCell i]
  rw [hSum] at hAll
  exact hAll.symm
