-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_grid_pair_count_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:42:10.29092+00:00
-- url     : https://prove2.me/submissions/9782e2d9-cd58-40e8-9dfd-1fb6588f18c0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original ceiling-mesh ordered pairs are a subset of actual chronological pairs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∀ (k : ℕ) (ω : Ω),
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞) ≤
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        p.1 < p.2)).card : ℕ) : ℝ≥0∞) := by
  classical
  dsimp only
  intro k ω
  have hTreal : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  have hcard :
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card ≤
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    rcases hp with ⟨hpair, hindex⟩
    refine ⟨hpair, ?_⟩
    by_contra hnlt
    have hle : p.2 ≤ p.1 := le_of_not_gt hnlt
    have hreal : (p.2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hle
    have hmul : (p.2 : ℝ) * (k : ℝ) ≤ (p.1 : ℝ) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right hreal (by positivity)
    have hdiv : ((p.2 : ℝ) * (k : ℝ)) / (T : ℝ) ≤
        ((p.1 : ℝ) * (k : ℝ)) / (T : ℝ) :=
      div_le_div_of_nonneg_right hmul (le_of_lt hTreal)
    have hceil := Nat.ceil_mono hdiv
    exact (not_lt_of_ge hceil) hindex
  change
    ((((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞) ≤
    ((((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℕ) : ℝ≥0∞)
  exact_mod_cast hcard
