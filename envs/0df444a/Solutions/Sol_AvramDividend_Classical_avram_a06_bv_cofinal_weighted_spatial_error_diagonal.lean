-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_bv_cofinal_weighted_spatial_error_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T14:18:05.0814+00:00
-- url     : https://prove2.me/submissions/b2ddcd8c-5a55-40c3-99ae-658b4075d3f8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_monotone_diagonal_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem solution
    (E : ℕ → ℕ → ℝ)
    (hE : ∀ n k, 0 ≤ E n k)
    (hTail : ∀ n, Tendsto (fun k => E n k) atTop (𝓝 (0 : ℝ)))
    (L : ℕ → ℝ) (hL : ∀ n, 0 ≤ L n) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧ (∀ n, n ≤ κ n) ∧
      Tendsto (fun n => (1 + L n) * E n (κ n))
        atTop (𝓝 (0 : ℝ))  := by
  have hPos (n k : ℕ) : 0 ≤ (1 + L n) * E n k :=
    mul_nonneg (by linarith [hL n]) (hE n k)
  have hZero (n : ℕ) :
      Tendsto (fun k => (1 + L n) * E n k)
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (hTail n) :
        Tendsto (fun k => (1 + L n) * E n k)
          atTop (𝓝 ((1 + L n) * (0 : ℝ))))
  exact avram_bv_strict6_monotone_diagonal_mean
    (fun n k => (1 + L n) * E n k) hPos hZero
