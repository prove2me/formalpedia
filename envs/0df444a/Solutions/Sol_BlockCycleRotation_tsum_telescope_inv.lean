-- Prove2me | solution 1 for BlockCycleRotation.tsum_telescope_inv
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T12:22:08.751928+00:00
-- url     : https://prove2.me/submissions/17f5a094-bcd7-460d-808c-be8afbd0540f

import Mathlib

open Real Finset Filter Topology

theorem solution {K : ℕ} (hK : 0 < K) :
    ∑' j : ℕ, (1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)) = 1 / (K : ℝ) := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hnn : ∀ j : ℕ, 0 ≤ 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1) := by
    intro j
    have h1 : (0 : ℝ) < (j : ℝ) + (K : ℝ) := by positivity
    have := one_div_le_one_div_of_le h1 (by linarith : (j : ℝ) + (K : ℝ) ≤ (j : ℝ) + (K : ℝ) + 1)
    linarith
  have hle : ∀ j : ℕ, 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)
      ≤ 1 / ((j : ℝ) + (K : ℝ)) ^ 2 := by
    intro j
    have h1 : (0 : ℝ) < (j : ℝ) + (K : ℝ) := by positivity
    have hrw : 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)
        = 1 / (((j : ℝ) + (K : ℝ)) * ((j : ℝ) + (K : ℝ) + 1)) := by
      field_simp
      ring
    rw [hrw]
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  have hgs : Summable (fun j : ℕ => 1 / ((j : ℝ) + (K : ℝ)) ^ 2) := by
    have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
      rw [Real.summable_one_div_nat_pow]; norm_num
    refine ((summable_nat_add_iff K).2 h0).congr fun j => ?_
    push_cast
    ring_nf
  have hs : Summable (fun j : ℕ => 1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1)) :=
    Summable.of_nonneg_of_le hnn hle hgs
  refine (hs.hasSum_iff_tendsto_nat.2 ?_).tsum_eq
  have hpart : ∀ N : ℕ, ∑ j ∈ Finset.range N,
      (1 / ((j : ℝ) + (K : ℝ)) - 1 / ((j : ℝ) + (K : ℝ) + 1))
      = 1 / (K : ℝ) - 1 / ((N : ℝ) + (K : ℝ)) := by
    intro N
    induction N with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hzero : Filter.Tendsto (fun N : ℕ => 1 / ((N : ℝ) + (K : ℝ))) Filter.atTop (nhds 0) := by
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    refine squeeze_zero (fun N => by positivity) (fun N => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hlim : Filter.Tendsto (fun N : ℕ => 1 / (K : ℝ) - 1 / ((N : ℝ) + (K : ℝ)))
      Filter.atTop (nhds (1 / (K : ℝ))) := by
    have h := Filter.Tendsto.sub (tendsto_const_nhds (x := 1 / (K : ℝ))) hzero
    rw [sub_zero] at h
    exact h
  exact hlim.congr (fun N => (hpart N).symm)
