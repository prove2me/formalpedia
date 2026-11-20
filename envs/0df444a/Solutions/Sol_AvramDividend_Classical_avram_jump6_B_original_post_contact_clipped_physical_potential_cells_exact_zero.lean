-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_post_contact_clipped_physical_potential_cells_exact_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:52:29.911677+00:00
-- url     : https://prove2.me/submissions/37e9dccf-9e1b-4b7a-b4ba-694544e78684

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false


theorem solution
    (n j : ℕ) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (k : ℕ)
    (hk : min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ = ρ)
    (l : ℕ) (hkl : k ≤ l)
    (x q : ℝ) (U A : ℝ≥0 → ℝ) (w : ℝ → ℝ) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ
    Real.exp (-(q * (v (l + 1) : ℝ))) *
      (w (x + U (v (l + 1)) - A (v (l + 1))) -
       w (x + U (v (l + 1)) - A (v l))) = 0 := by
  dsimp
  have hρk :
      ρ ≤ (k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) := by
    exact (min_eq_right_iff).mp hk
  have hρl (i : ℕ) (hi : k ≤ i) :
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ρ = ρ := by
    apply min_eq_right
    apply hρk.trans
    exact div_le_div_of_nonneg_right (by exact_mod_cast hi) (by positivity)
  rw [hρl l hkl, hρl (l + 1) (Nat.le_succ_of_le hkl)]
  ring