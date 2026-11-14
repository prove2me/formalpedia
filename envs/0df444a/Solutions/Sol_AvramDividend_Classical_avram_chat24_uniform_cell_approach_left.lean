-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_uniform_cell_approach_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:00:58.22953+00:00
-- url     : https://prove2.me/submissions/7a1e02e5-f5bf-4bd0-b176-e6d6faf5b937

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (B t : ℝ≥0) (k : ℕ → ℕ)
    (hcell : ∀ n : ℕ,
      B * (k n : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0) < t ∧
      t ≤ B * ((k n + 1 : ℕ) : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)) :
    Tendsto (fun n : ℕ => B * (k n : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0))
      atTop (𝓝[<] t) := by
  let u (n i : ℕ) : ℝ≥0 := B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
  change Tendsto (fun n => u n (k n)) atTop (𝓝[<] t)
  have hstep (n j : ℕ) : u n (j + 1) = u n j + B / ((n + 1 : ℕ) : ℝ≥0) := by
    simp [u, Nat.cast_add, mul_add, add_div]
  have hbound (n : ℕ) :
      (t : ℝ) - (u n (k n) : ℝ) ≤ (B : ℝ) / ((n : ℝ) + 1) := by
    have hr : (t : ℝ) ≤ (u n (k n + 1) : ℝ) := by exact_mod_cast (hcell n).2
    have hs : (u n (k n + 1) : ℝ) =
        (u n (k n) : ℝ) + (B : ℝ) / ((n : ℝ) + 1) := by
      exact_mod_cast hstep n (k n)
    linarith
  have heB : Tendsto (fun n : ℕ => (B : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
    have hc : Tendsto (fun _ : ℕ => (B : ℝ)) atTop (nhds (B : ℝ)) := tendsto_const_nhds
    simpa [div_eq_mul_inv] using hc.mul tendsto_one_div_add_atTop_nhds_zero_nat
  have he : Tendsto (fun n => (t : ℝ) - (u n (k n) : ℝ)) atTop (nhds 0) :=
    squeeze_zero (fun n => sub_nonneg.mpr (by exact_mod_cast (hcell n).1.le)) hbound heB
  have hc : Tendsto (fun n => (u n (k n) : ℝ)) atTop (nhds (t : ℝ)) := by
    have hc : Tendsto (fun _ : ℕ => (t : ℝ)) atTop (nhds (t : ℝ)) := tendsto_const_nhds
    simpa only [sub_sub_cancel, sub_zero] using hc.sub he
  exact tendsto_nhdsWithin_iff.2
    ⟨tendsto_subtype_rng.2 hc, Filter.Eventually.of_forall (fun n => (hcell n).1)⟩
