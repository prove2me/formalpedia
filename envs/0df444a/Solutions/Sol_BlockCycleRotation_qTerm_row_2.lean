-- Prove2me | solution 2 for BlockCycleRotation.qTerm_row
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T11:43:45.654066+00:00
-- url     : https://prove2.me/submissions/797e6216-74c7-4a28-a6c3-20c1f3e2c8b4

import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open BlockCycleRotation
open Real Finset Filter Topology

theorem solution (i : ℕ) : ∑' j : ℕ, qTerm (i, j) = harm (i + 2) / ((i : ℝ) + 1) ^ 2 := by
  have harm_eq_range (n : ℕ) : harm (n + 1) = ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) := by
    unfold harm
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring_nf

  have telescope_partial (n N : ℕ) (h : n ≤ N) :
      ∑ j ∈ Finset.range N, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1))
        = (∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1))
          - ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1) := by
    have h1 : ∑ j ∈ Finset.range N, 1 / ((j : ℝ) + (n : ℝ) + 1)
        = ∑ j ∈ Finset.Ico n (N + n), 1 / ((j : ℝ) + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring_nf
    rw [Finset.sum_sub_distrib, h1, Finset.range_eq_Ico, Finset.range_eq_Ico]
    have s1 : (∑ j ∈ Finset.Ico 0 n, 1 / ((j : ℝ) + 1))
        + ∑ j ∈ Finset.Ico n N, 1 / ((j : ℝ) + 1)
        = ∑ j ∈ Finset.Ico 0 N, 1 / ((j : ℝ) + 1) :=
      Finset.sum_Ico_consecutive _ (Nat.zero_le n) h
    have s2 : (∑ j ∈ Finset.Ico n N, 1 / ((j : ℝ) + 1))
        + ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)
        = ∑ j ∈ Finset.Ico n (N + n), 1 / ((j : ℝ) + 1) :=
      Finset.sum_Ico_consecutive _ h (by omega)
    linarith

  have tendsto_window (n : ℕ) :
      Tendsto (fun N : ℕ => ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    have hz : Tendsto (fun N : ℕ => (n : ℝ) * (1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
      have h : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 := h.const_mul (n : ℝ)
      rw [mul_zero] at h2
      exact h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
      (fun N => Finset.sum_nonneg fun j _ => by positivity) (fun N => ?_)
    calc ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)
        ≤ ∑ _j ∈ Finset.Ico N (N + n), 1 / ((N : ℝ) + 1) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_Ico] at hj
          have : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
          exact one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = (n : ℝ) * (1 / ((N : ℝ) + 1)) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
          simp

  have tsum_telescope (n : ℕ) :
      ∑' j : ℕ, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1))
        = ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) := by
    have hsum : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1)) := by
      have hg : Summable (fun j : ℕ => (n : ℝ) * (1 / ((j : ℝ) + 1) ^ 2)) := by
        have h : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
          have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
            rw [Real.summable_one_div_nat_pow]; norm_num
          refine ((summable_nat_add_iff 1).2 h0).congr fun j => ?_
          push_cast; ring
        exact h.mul_left _
      refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hg
      · have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
        have h1 : 1 / ((j : ℝ) + (n : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith
      · have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
        have hjn : (0 : ℝ) < (j : ℝ) + (n : ℝ) + 1 := by positivity
        have key : 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1)
            = (n : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + (n : ℝ) + 1)) := by
          field_simp
          ring
        have hr : (n : ℝ) * (1 / ((j : ℝ) + 1) ^ 2) = (n : ℝ) / ((j : ℝ) + 1) ^ 2 := by ring
        rw [key, hr]
        gcongr
        nlinarith
    refine (hsum.hasSum_iff_tendsto_nat.2 ?_).tsum_eq
    have heq : (fun N : ℕ => ∑ j ∈ Finset.range N,
          (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1)))
        =ᶠ[atTop] (fun N : ℕ => (∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1))
          - ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)) := by
      filter_upwards [eventually_ge_atTop n] with N hN
      exact telescope_partial n N hN
    refine Tendsto.congr' heq.symm ?_
    have hlim : Tendsto (fun N : ℕ => (∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1))
        - ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)) atTop
        (𝓝 ((∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1)) - 0)) :=
      tendsto_const_nhds.sub (tendsto_window n)
    rw [sub_zero] at hlim
    exact hlim

  have hn : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hc : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  have heq : ∀ j : ℕ, qTerm (i, j)
      = (1 / ((i : ℝ) + 1) ^ 2)
        * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + ((i + 1 : ℕ) : ℝ) + 1)) := by
    intro j
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hjn : (0 : ℝ) < (j : ℝ) + ((i : ℝ) + 1) + 1 := by positivity
    rw [hc]
    unfold qTerm
    field_simp
    ring
  rw [tsum_congr heq, tsum_mul_left, tsum_telescope (i + 1), ← harm_eq_range]
  ring
