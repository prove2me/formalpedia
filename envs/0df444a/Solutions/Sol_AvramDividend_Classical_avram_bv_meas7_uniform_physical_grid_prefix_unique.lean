-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_uniform_physical_grid_prefix_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:34:30.11965+00:00
-- url     : https://prove2.me/submissions/400d926c-3247-4648-a860-86ba5399233c

import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_prefix_uniform_physical_grid
import Mathlib.Data.NNReal.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Two original strict-prefix uniform physical meshes with the same
zero clock and exact increment agree on every active prefix cell. -/
theorem solution
    (T : ℝ) (u v : ℕ → ℕ → ℝ≥0)
    (hu0 : ∀ n, u n 0 = 0) (hv0 : ∀ n, v n 0 = 0)
    (huWidth : ∀ n i, i < n + 1 →
      (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2))
    (hvWidth : ∀ n i, i < n + 1 →
      (v n (i + 1) : ℝ) - (v n i : ℝ) = T / ((n : ℝ) + 2)) :
    ∀ n i, i ≤ n + 1 → u n i = v n i := by
  intro n i
  induction i with
  | zero =>
      intro _
      rw [hu0 n, hv0 n]
  | succ j ih =>
      intro hi
      have hj : j < n + 1 := by omega
      have hprev : u n j = v n j := ih (Nat.le_of_lt hj)
      have hu := huWidth n j hj
      have hv := hvWidth n j hj
      have hprevR : (u n j : ℝ) = (v n j : ℝ) :=
        congrArg (fun z : ℝ≥0 => (z : ℝ)) hprev
      apply NNReal.coe_injective
      linarith
