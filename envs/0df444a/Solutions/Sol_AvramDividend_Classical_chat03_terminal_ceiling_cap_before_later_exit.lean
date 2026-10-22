-- Prove2me | solution 1 for AvramDividend.Classical.chat03_terminal_ceiling_cap_before_later_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T20:42:13.217115+00:00
-- url     : https://prove2.me/submissions/51c667e2-0e09-46aa-a202-6b04bd9e1d66

import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LeftRightNhds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
The final uniform-grid sample obtained by taking the ceiling of a
finite horizon T eventually lies before every later finite exit τ>T.
The result uses only the exact ceiling bracket and vanishing mesh.
-/
theorem solution
    (T τ : ℝ≥0) (hT : T < τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n) :
    ∀ᶠ n in atTop,
      T ≤ (Nat.ceil (T / mesh n) : ℝ≥0) * mesh n ∧
      (Nat.ceil (T / mesh n) : ℝ≥0) * mesh n < τ := by
  have hε : 0 < τ - T := tsub_pos_of_lt hT
  have hIio : Set.Iio (τ - T) ∈ 𝓝 (0 : ℝ≥0) :=
    isOpen_Iio.mem_nhds hε
  have hsum : T + (τ - T) = τ := by
    simpa only [add_comm] using
      (tsub_add_cancel_of_le (le_of_lt hT))
  filter_upwards [hmesh.eventually hIio] with n hn
  obtain ⟨hlower, hupper⟩ :=
    chat03_nnreal_grid_ceiling_bracket T (mesh n) (hpos n)
  refine ⟨hlower, ?_⟩
  calc
    (Nat.ceil (T / mesh n) : ℝ≥0) * mesh n <
        T + mesh n := hupper
    _ < T + (τ - T) := by
        simpa only [add_comm] using (add_lt_add_left hn T)
    _ = τ := hsum
