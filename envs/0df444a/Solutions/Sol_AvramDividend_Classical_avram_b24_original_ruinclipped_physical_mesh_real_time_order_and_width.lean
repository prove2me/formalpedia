-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_ruinclipped_physical_mesh_real_time_order_and_width
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:35:47.324895+00:00
-- url     : https://prove2.me/submissions/d081ddde-93fe-4fd0-b50c-a1f1b21ccb66

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (n m i : ℕ) (σ : ℝ≥0) (hσ : σ ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * Δ) σ
    v i ≤ v (i + 1) ∧ v (i + 1) ≤ (n : ℝ≥0) ∧
      (((v (i + 1) - v i : ℝ≥0) : ℝ)) =
        (v (i + 1) : ℝ) - (v i : ℝ) := by
  intro Δ v
  have hi : (i : ℝ≥0) ≤ ((i + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.le_succ i
  have hprod : (i : ℝ≥0) * Δ ≤ ((i + 1 : ℕ) : ℝ≥0) * Δ :=
    mul_le_mul_of_nonneg_right hi bot_le
  have horder : v i ≤ v (i + 1) :=
    min_le_min_right σ hprod
  have hcap : v (i + 1) ≤ (n : ℝ≥0) :=
    (min_le_right _ _).trans hσ
  exact ⟨horder, hcap, NNReal.coe_sub horder⟩
