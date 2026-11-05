-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_marked_pair_strict_mesh_index
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:37:14.157199+00:00
-- url     : https://prove2.me/submissions/75f0b571-d6cc-4d79-ab25-963d06f7f80a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_marked_pairs_uniform_grid_scale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∃ k : ℕ, 0 < k ∧
      ∀ u ∈ F, ∀ v ∈ F, u < v →
        Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) := by
  dsimp only
  obtain ⟨k, hk, hsep⟩ :=
    avram_p4_f_assembly_original_marked_pairs_uniform_grid_scale X ω T n
  refine ⟨k, hk, ?_⟩
  intro u hu v hv huv
  have hTreal : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hsep' := hsep u hu v hv huv
  have hmid : (u : ℝ) * (k : ℝ) + (T : ℝ) <
      (v : ℝ) * (k : ℝ) := by nlinarith
  have hdiv : ((u : ℝ) * (k : ℝ) + (T : ℝ)) / (T : ℝ) <
      ((v : ℝ) * (k : ℝ)) / (T : ℝ) :=
    div_lt_div_of_pos_right hmid hTreal
  have hscaled : ((u : ℝ) * (k : ℝ)) / (T : ℝ) + 1 <
      ((v : ℝ) * (k : ℝ)) / (T : ℝ) := by
    convert hdiv using 1 <;> field_simp <;> ring
  have ha : (0 : ℝ) ≤ ((u : ℝ) * (k : ℝ)) / (T : ℝ) := by positivity
  have huceil : ((Nat.ceil (((u : ℝ) * (k : ℝ)) / (T : ℝ))) : ℝ) <
      ((u : ℝ) * (k : ℝ)) / (T : ℝ) + 1 :=
    Nat.ceil_lt_add_one ha
  have hvceil : ((v : ℝ) * (k : ℝ)) / (T : ℝ) ≤
      ((Nat.ceil (((v : ℝ) * (k : ℝ)) / (T : ℝ))) : ℝ) :=
    Nat.le_ceil _
  exact_mod_cast lt_trans huceil (lt_of_lt_of_le hscaled hvceil)
