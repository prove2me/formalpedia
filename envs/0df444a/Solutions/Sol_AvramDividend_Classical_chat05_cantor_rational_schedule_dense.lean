-- Prove2me | solution 1 for AvramDividend.Classical.chat05_cantor_rational_schedule_dense
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T11:37:14.219836+00:00
-- url     : https://prove2.me/submissions/bc621dee-9bb8-4be8-8b32-5b87319565a5

import Mathlib.Topology.Closure
import Mathlib.Topology.Neighborhoods
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Mathlib.Algebra.Order.Floor.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The explicit rational Cantor-pairing clock is dense in nonnegative time. -/
theorem solution :
    Dense (Set.range (fun j : ℕ =>
      ((Nat.unpair j).2 : ℝ≥0) *
        (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹))) := by
  apply dense_iff_closure_eq.mpr
  apply Set.eq_univ_iff_forall.mpr
  intro t
  let u : ℕ → ℝ≥0 := fun n =>
    (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
  have hu : ∀ n : ℕ, u n ∈ Set.range (fun j : ℕ =>
      ((Nat.unpair j).2 : ℝ≥0) *
        (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) := by
    intro n
    have hn : 0 < (2 : ℕ) ^ n := pow_pos (by decide) n
    obtain ⟨j, hj⟩ :=
      chat04_nat_pairing_rational_grid_coverage ((2 : ℕ) ^ n)
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n)) hn
    refine ⟨j, ?_⟩
    simpa only [u, div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat] using hj
  have hlim : Tendsto u atTop (𝓝 t) :=
    dyadic_ceiling_nnreal_tendsto t
  exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall hu)
