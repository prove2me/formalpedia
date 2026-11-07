-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_monotone_diagonal_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:33:08.974351+00:00
-- url     : https://prove2.me/submissions/f29be264-9899-4490-9e8b-a594f0512363

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_diagonal_nonnegative_error_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter AvramDividend.Classical
open scoped Topology
noncomputable section

/-- A strictly increasing original-source grid selector with vanishing mean error. -/
theorem solution
    (E : ℕ → ℕ → ℝ)
    (hnonneg : ∀ k n, 0 ≤ E k n)
    (hvanish : ∀ k, Tendsto (fun n => E k n) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ k, k ≤ φ k) ∧
      Tendsto (fun k => E k (φ k)) atTop (𝓝 0) := by
  have hthreshold :
      ∀ k : ℕ, ∃ N : ℕ,
        ∀ n ≥ N, E k n < (1 : ℝ) / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hev : ∀ᶠ n : ℕ in atTop,
        |E k n| < 1 / ((k : ℝ) + 1) := by
      have hmetric := (Metric.tendsto_nhds.mp (hvanish k)) _ hpos
      simpa only [Real.dist_eq, sub_zero] using hmetric
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    exact ⟨N, fun n hn => lt_of_le_of_lt (le_abs_self (E k n)) (hN n hn)⟩
  choose N hN using hthreshold
  let φ : ℕ → ℕ :=
    Nat.rec (N 0) (fun k previous => max (N (k + 1)) (previous + 1))
  have hstep (k : ℕ) :
      φ (k + 1) = max (N (k + 1)) (φ k + 1) := rfl
  have hφN : ∀ k, N k ≤ φ k := by
    intro k
    cases k with
    | zero => exact le_rfl
    | succ k =>
      rw [hstep]
      exact le_max_left _ _
  have hφstrict : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro k
    rw [hstep]
    exact (Nat.lt_succ_self (φ k)).trans_le (le_max_right _ _)
  have hφindex : ∀ k, k ≤ φ k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      calc
        k + 1 ≤ φ k + 1 := Nat.succ_le_succ ih
        _ ≤ max (N (k + 1)) (φ k + 1) := le_max_right _ _
        _ = φ (k + 1) := (hstep k).symm
  refine ⟨φ, hφstrict, hφindex, ?_⟩
  have hUpper : Tendsto
      (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1))
      atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply Filter.Tendsto.squeeze tendsto_const_nhds hUpper
  · intro k
    exact hnonneg k (φ k)
  · intro k
    exact le_of_lt (hN k (φ k) (hφN k))
