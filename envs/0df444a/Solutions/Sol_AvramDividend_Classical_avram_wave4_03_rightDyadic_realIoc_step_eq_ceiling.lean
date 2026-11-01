-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_rightDyadic_realIoc_step_eq_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:25:52.664613+00:00
-- url     : https://prove2.me/submissions/d639af1a-eaa4-44ca-83a6-248119364a0c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_cell_indicator_sum_eq_ceiling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Right mesh endpoint precisely equals the full Ioc-cell step value. -/
theorem solution (T s : ℝ) (hT : 0 < T) (hs : 0 < s) (hsT : s ≤ T)
    (N : ℕ) (hN : 0 < N) (a : ℕ → ℝ≥0∞) :
    (∑ i ∈ Finset.range N,
      if s ∈ Ioc ((i : ℝ) * T / (N : ℝ))
        (((i + 1 : ℕ) : ℝ) * T / (N : ℝ))
      then a (i + 1) else 0) =
    a (Nat.ceil ((s / T) * (N : ℝ))) := by
  classical
  have hy : 0 < s / T := div_pos hs hT
  have hy1 : s / T ≤ 1 := (div_le_one hT).2 hsT
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have heq (i : ℕ) :
      s ∈ Ioc ((i : ℝ) * T / (N : ℝ))
        (((i + 1 : ℕ) : ℝ) * T / (N : ℝ)) ↔
      (i : ℝ) < (s / T) * (N : ℝ) ∧
      (s / T) * (N : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
    simp only [Set.mem_Ioc]
    have hscale : (s / T) * (N : ℝ) = s * (N : ℝ) / T := by ring
    rw [hscale]
    constructor
    · rintro ⟨hl, hr⟩
      exact ⟨(lt_div_iff₀ hT).2 ((div_lt_iff₀ hNreal).1 hl),
        (div_le_iff₀ hT).2 ((le_div_iff₀ hNreal).1 hr)⟩
    · rintro ⟨hl, hr⟩
      exact ⟨(div_lt_iff₀ hNreal).2 ((lt_div_iff₀ hT).1 hl),
        (le_div_iff₀ hNreal).2 ((div_le_iff₀ hT).1 hr)⟩
  simp_rw [heq]
  exact avram_wave4_03_rightDyadic_cell_indicator_sum_eq_ceiling
    (s / T) hy hy1 N hN a
