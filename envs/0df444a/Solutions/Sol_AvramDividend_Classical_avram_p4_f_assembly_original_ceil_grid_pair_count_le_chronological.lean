-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_ceil_grid_pair_count_le_chronological
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:01:37.094078+00:00
-- url     : https://prove2.me/submissions/9bf83e41-2457-412d-9156-ca6c7e790b4b

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem solution
    (F : Finset ℝ≥0) (T : ℝ≥0) (hT : 0 < T) (k : ℕ) :
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card ≤
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, ?_⟩
  by_contra hnot
  have hle : p.2 ≤ p.1 := le_of_not_gt hnot
  have hleR : (p.2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hle
  have hmul : (p.2 : ℝ) * (k : ℝ) ≤ (p.1 : ℝ) * (k : ℝ) :=
    mul_le_mul_of_nonneg_right hleR (Nat.cast_nonneg k)
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hdiv :
      (p.2 : ℝ) * (k : ℝ) / (T : ℝ) ≤
      (p.1 : ℝ) * (k : ℝ) / (T : ℝ) :=
    div_le_div_of_nonneg_right hmul (le_of_lt hTreal)
  have hceil := Nat.ceil_mono hdiv
  exact (not_lt_of_ge hceil) hp.2
