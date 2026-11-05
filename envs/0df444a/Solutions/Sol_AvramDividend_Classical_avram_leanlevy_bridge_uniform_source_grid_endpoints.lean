-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_uniform_source_grid_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:40:07.446304+00:00
-- url     : https://prove2.me/submissions/6de811b9-a862-4ec0-9dfa-e41289080b2d

import Mathlib.Data.NNReal.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section
theorem solution
    (T : ℝ≥0) (k : ℕ) (hk : 0 < k) :
    let s : Fin k → ℝ≥0 := fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    (∀ i, s i ≤ t i) ∧ (∀ i, t i ≤ T) ∧
    (∀ i, (s i : ℝ) = (i.val : ℝ) * (T : ℝ) / (k : ℝ)) ∧
    (∀ i, (t i : ℝ) = ((i.val + 1 : ℕ) : ℝ) * (T : ℝ) / (k : ℝ)) := by
  dsimp only
  have hkpos : (0 : ℝ≥0) < (k : ℝ≥0) := by exact_mod_cast hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    apply div_le_div_of_nonneg_right
    · apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.le_succ i.val
      · exact zero_le
    · exact zero_le
  · intro i
    have hi : (i.val + 1 : ℕ) ≤ k := Nat.succ_le_of_lt i.isLt
    have hni : (((i.val + 1 : ℕ) : ℝ≥0) ≤ (k : ℝ≥0)) := by
      exact_mod_cast hi
    apply (div_le_iff₀ hkpos).mpr
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_right hni (show (0 : ℝ≥0) ≤ T from zero_le))
  · intro i
    norm_cast
  · intro i
    norm_cast