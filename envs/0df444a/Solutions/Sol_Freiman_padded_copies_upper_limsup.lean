-- Prove2me | solution 1 for Freiman.padded_copies_upper_limsup
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:25.864677+00:00
-- url     : https://prove2.me/submissions/25e39f72-7a26-4f9a-ac85-e5be123be784

import Definitions.Def_Freiman_paddedCopies
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_Freiman_padded_copies_local_upper
import Theorems.Thm_Freiman_cylinder_bound_tendsto
import Mathlib.Tactic.Linarith

open Freiman
set_option autoImplicit false

theorem solution (a : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+) (d : ℕ+) (t : ℝ) (ε : ℕ → ℝ)
    (hcopy : PaddedCopies a b d)
    (hpad : ∀ j : ℕ, ∀ i : ℤ, j < i.natAbs → a j i = d)
    (hbound : ∀ j : ℕ, ∀ i : ℤ, localValue (a j) i ≤ t + ε j)
    (heps : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hbackground : Real.sqrt ((((d : ℕ) : ℝ) ^ 2) + 4) ≤ t) :
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → localValue b (n : ℤ) ≤ t + η := by
  intro η hη
  have hhalf : 0 < η / 2 := half_pos hη
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.mp cylinder_bound_tendsto (η / 2) hhalf
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp heps (η / 2) hhalf
  have hJR : ∀ j : ℕ, J ≤ j → ε j ≤ η / 2 := by
    intro j hj
    have hh := hJ j hj
    rw [Real.dist_eq, sub_zero] at hh
    exact (abs_lt.mp hh).2.le
  obtain ⟨N, hN⟩ := padded_copies_local_upper a b d t ε hcopy hpad hbound hbackground R J (η / 2) hhalf.le hJR
  refine ⟨N, ?_⟩
  intro n hn
  have hh := hR R le_rfl
  rw [Real.dist_eq, sub_zero] at hh
  have hb := (abs_lt.mp hh).2
  linarith [hN n hn]
