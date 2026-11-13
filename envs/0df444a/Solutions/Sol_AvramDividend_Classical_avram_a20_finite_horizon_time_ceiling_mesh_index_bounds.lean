-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_finite_horizon_time_ceiling_mesh_index_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T15:53:17.692237+00:00
-- url     : https://prove2.me/submissions/152541bc-e832-47c2-a4b7-164f5c616cce

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section

theorem solution
    (u T : ℝ≥0) (hT : 0 < T)
    (hu : 0 < u) (huT : u ≤ T)
    (k : ℕ) (hk : 0 < k) :
    0 < Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ∧
      Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ k := by
  have hTreal : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hu0real : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hkreal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hscaledPos : (0 : ℝ) <
      (u : ℝ) * (k : ℝ) / (T : ℝ) := by positivity
  have hnatPos :
      0 < Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) := by
    by_contra hh
    have hz : Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) = 0 :=
      Nat.eq_zero_of_not_pos hh
    have hceil := Nat.le_ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))
    have hbad : (u : ℝ) * (k : ℝ) / (T : ℝ) ≤ 0 := by
      simpa [hz] using hceil
    exact (not_le_of_gt hscaledPos) hbad
  have huTR : (u : ℝ) ≤ (T : ℝ) := by exact_mod_cast huT
  have hmul := mul_le_mul_of_nonneg_right huTR (le_of_lt hkreal)
  have hscaledLe :
      (u : ℝ) * (k : ℝ) / (T : ℝ) ≤ (k : ℝ) := by
    apply (div_le_iff₀ hTreal).mpr
    nlinarith [hmul]
  exact ⟨hnatPos, Nat.ceil_le.mpr hscaledLe⟩
