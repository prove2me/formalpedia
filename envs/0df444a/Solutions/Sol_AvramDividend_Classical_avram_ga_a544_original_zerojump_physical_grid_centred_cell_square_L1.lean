-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a544_original_zerojump_physical_grid_centred_cell_square_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:53:09.064719+00:00
-- url     : https://prove2.me/submissions/cd1cd772-f808-4aed-8907-eeeb76fac0a9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a542_original_zerojump_gaussian_centred_increment_square_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n m i : ℕ) (hi : i < m) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    Integrable (fun ω =>
      (X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c)^2) P := by
  dsimp only
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i : ℝ≥0) * Δ
  have hden : 0 < (m : ℝ≥0) + 1 := by positivity
  have ht : s + Δ ≤ (n : ℝ≥0) := by
    have hfactor : (i : ℝ≥0) + 1 ≤ (m : ℝ≥0) + 1 := by
      exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt hi) 1
    calc
      s + Δ = ((i : ℝ≥0) + 1) * Δ := by dsimp [s]; ring
      _ ≤ ((m : ℝ≥0) + 1) * Δ := by gcongr
      _ = n := by dsimp [Δ]; field_simp [ne_of_gt hden]
  have hs : s ≤ (n : ℝ≥0) :=
    le_trans (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ Δ)) ht
  have hI := avram_ga_a542_original_zerojump_gaussian_centred_increment_square_L1
    X hNuZero (n : ℝ≥0) s (s+Δ) hs ht
  have hEq (ω : Ω) :
      (X.X (s+Δ) ω - X.X s ω - (Δ : ℝ)*X.c)^2 =
      ((X.X (s+Δ) ω - ((s+Δ : ℝ≥0) : ℝ)*X.c) -
        (X.X s ω - (s : ℝ)*X.c))^2 := by
    push_cast
    ring
  exact hI.congr (Filter.Eventually.of_forall fun ω => (hEq ω).symm)
