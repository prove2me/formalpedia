-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_marked_pairs_unit_mesh_bracket
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:12:30.9247+00:00
-- url     : https://prove2.me/submissions/0b57e9b4-930f-4c0a-ac95-1fea19ef6053

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_times_chronological_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧
      ∀ u ∈ F, ∀ v ∈ F, u < v →
        ∃ i : ℕ, (u : ℝ) ≤ (i : ℝ) / (k : ℝ) ∧
          (i : ℝ) / (k : ℝ) < (v : ℝ) := by
  dsimp only
  obtain ⟨δ, hδ, hgap⟩ :=
    avram_p4_f_assembly_original_marked_times_chronological_gap X ω T n
  obtain ⟨k, hk⟩ := exists_nat_gt ((1 : ℝ) / δ)
  let m : ℕ := k + 1
  have hmpos : 0 < m := Nat.succ_pos k
  have hmposR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hk' : (1 : ℝ) / δ < (m : ℝ) :=
    lt_of_lt_of_le hk (by exact_mod_cast Nat.le_succ k)
  have hmδ : (1 : ℝ) < (m : ℝ) * δ :=
    (div_lt_iff₀ hδ).mp hk'
  refine ⟨m, hmpos, ?_⟩
  intro u hu v hv huv
  let i : ℕ := Nat.ceil ((u : ℝ) * (m : ℝ))
  have hc1 : (u : ℝ) * (m : ℝ) ≤ (i : ℝ) := Nat.le_ceil _
  have hnonneg : (0 : ℝ) ≤ (u : ℝ) * (m : ℝ) := by positivity
  have hc2 : (i : ℝ) < (u : ℝ) * (m : ℝ) + 1 :=
    Nat.ceil_lt_add_one hnonneg
  have hg : δ ≤ (v : ℝ) - (u : ℝ) :=
    hgap u hu v hv huv
  have hscaled : (1 : ℝ) < (m : ℝ) * ((v : ℝ) - (u : ℝ)) := by
    calc
      1 < (m : ℝ) * δ := hmδ
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (le_of_lt hmposR)
  refine ⟨i, ?_, ?_⟩
  · apply (le_div_iff₀ hmposR).mpr
    nlinarith [hc1]
  · apply (div_lt_iff₀ hmposR).mpr
    nlinarith [hc2, hscaled]
