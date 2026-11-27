-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_uniform_grid_properties
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:18:36.690469+00:00
-- url     : https://prove2.me/submissions/15af5363-26d4-4227-9a44-86c5f2598f67

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    (H : ℝ≥0) (m : ℕ → ℕ) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => (i : ℝ≥0) * H / ((m n : ℝ≥0) + 1)
    let k : ℕ → ℕ := fun n => m n + 1
    (∀ n, Monotone (u n)) ∧ (∀ n, u n 0 = 0) ∧ (∀ n, u n (k n) = H) := by 
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro n i j hij
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (show 0 ≤ H from zero_le)) (by positivity)
  · intro n
    simp
  · intro n
    push_cast
    field_simp
