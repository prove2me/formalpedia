-- Prove2me | solution 1 for CondatPD.FinDim.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:12:34.887016+00:00
-- url     : https://prove2.me/submissions/77ba539e-0a5a-4ae6-a5e7-0d02ecbec7e8

import Mathlib

open Filter Topology

open Filter Topology in
theorem solution (a b c : ℕ → ℝ)
    (h1 : ∀ n, 0 ≤ a n ∧ 0 ≤ c n ∧ c n < 1 ∧ 0 ≤ b n)
    (h2 : ∀ n, a (n + 1) ≤ c n * a n + b n)
    (h3 : Tendsto (fun N => ∑ n ∈ Finset.range N, (1 - c n)) atTop atTop)
    (h4 : Tendsto (fun n => b n / (1 - c n)) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hεpos : 0 < δ / 3 := by positivity
  set ε := δ / 3 with hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h4) ε hεpos
  have hb : ∀ n ≥ N, b n ≤ ε * (1 - c n) := by
    intro n hn
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    have hc : 0 < 1 - c n := by linarith [(h1 n).2.2.1]
    have h' := (abs_lt.1 h).2
    rw [div_lt_iff₀ hc] at h'
    linarith
  set S : ℕ → ℝ := fun M => ∑ n ∈ Finset.range M, (1 - c n) with hS
  have key : ∀ m, N ≤ m →
      max (a m - ε) 0 ≤ max (a N - ε) 0 * Real.exp (-(S m - S N)) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have hc0 := (h1 m).2.1
      have hstep : max (a (m+1) - ε) 0 ≤ c m * max (a m - ε) 0 := by
        apply max_le
        · have e1 := h2 m
          have e2 := hb m hm
          have e3 := mul_le_mul_of_nonneg_left (le_max_left (a m - ε) 0) hc0
          nlinarith
        · exact mul_nonneg hc0 (le_max_right _ _)
      have hcexp : c m ≤ Real.exp (c m - 1) := by
        have := Real.add_one_le_exp (c m - 1); linarith
      have hSs : S (m+1) = S m + (1 - c m) := by
        simp only [hS]; rw [Finset.sum_range_succ]
      calc max (a (m+1) - ε) 0 ≤ c m * max (a m - ε) 0 := hstep
        _ ≤ Real.exp (c m - 1) * (max (a N - ε) 0 * Real.exp (-(S m - S N))) :=
            mul_le_mul hcexp ih (le_max_right _ _) (Real.exp_pos _).le
        _ = max (a N - ε) 0 * Real.exp (-(S (m+1) - S N)) := by
            rw [hSs, mul_left_comm, ← Real.exp_add]
            congr 2
            ring
  have hT1 : Tendsto (fun m => S m - S N) atTop atTop :=
    tendsto_atTop_add_const_right _ _ h3
  have hT : Tendsto (fun m => max (a N - ε) 0 * Real.exp (-(S m - S N))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hT1).const_mul (max (a N - ε) 0)
    simpa using this
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hT.eventually (gt_mem_nhds hεpos))
  refine ⟨max N M, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnM : M ≤ n := le_trans (le_max_right _ _) hn
  have k1 := key n hnN
  have k2 := hM n hnM
  have k3 := le_max_left (a n - ε) 0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (h1 n).1]
  linarith
