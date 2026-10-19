-- Prove2me | solution 1 for ClassNumberFormula.residue_eq_average_of_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:31:33.693475+00:00
-- url     : https://prove2.me/submissions/320fdbe9-092f-4249-ac3f-640858bbe7c5

import Mathlib

open Filter Topology

theorem solution (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ρ : ℝ)
    (h : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, a n) / (N : ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * LSeries (fun n => (a n : ℂ)) s) (𝓝[>] 1)
      (𝓝 (ρ : ℂ)) :=
  LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg a h ha
