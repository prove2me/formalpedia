-- Prove2me | solution 1 for AvramDividend.Classical.renewal_quotient_pointwise_bound_of_finite_cycle_sums
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:58:43.202505+00:00
-- url     : https://prove2.me/submissions/d45e5fcb-a46f-4114-9847-cd1cf4d2dfdc

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal


theorem solution (V : ℝ≥0∞) (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hr : ∀ ε : ℝ, 0 < ε → ε < a → 0 ≤ W (a - ε) / W a ∧ W (a - ε) / W a < 1)
    (hfin : ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < a →
      ∑ k ∈ Finset.range N,
        ENNReal.ofReal ε * (ENNReal.ofReal (W (a - ε) / W a)) ^ (k + 1) ≤ V) :
    ∀ ε : ℝ, 0 < ε → ε < a →
      ENNReal.ofReal (ε * (W (a - ε) / W a) / (1 - W (a - ε) / W a)) ≤ V := by
  intro ε hε0 hεa
  obtain ⟨hr0, hr1⟩ := hr ε hε0 hεa
  have hne : (1:ℝ) - W (a-ε)/W a ≠ 0 := by
    intro hcon
    have h1 : W (a-ε)/W a = 1 := by linarith
    linarith
  have hpow : Filter.Tendsto (fun N : ℕ => (W (a-ε)/W a) ^ N) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hclosed : ∀ N : ℕ, ∑ k ∈ Finset.range N, ε * (W (a-ε)/W a) ^ (k+1)
      = ε * (W (a-ε)/W a) * ((1 - (W (a-ε)/W a) ^ N) / (1 - W (a-ε)/W a)) := by
    intro N
    have hgs : (∑ k ∈ Finset.range N, (W (a-ε)/W a) ^ k) * (1 - W (a-ε)/W a)
        = 1 - (W (a-ε)/W a) ^ N := geom_sum_mul_neg _ N
    have hfac : ∑ k ∈ Finset.range N, ε * (W (a-ε)/W a) ^ (k+1)
        = ε * (W (a-ε)/W a) * ∑ k ∈ Finset.range N, (W (a-ε)/W a) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ]
      ring
    have hsum : ∑ k ∈ Finset.range N, (W (a-ε)/W a) ^ k
        = (1 - (W (a-ε)/W a) ^ N) / (1 - W (a-ε)/W a) := by
      rw [eq_div_iff hne]
      linarith [hgs]
    rw [hfac, hsum]
  have hlimR : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, ε * (W (a-ε)/W a) ^ (k+1))
      Filter.atTop (𝓝 (ε * (W (a-ε)/W a) / (1 - W (a-ε)/W a))) := by
    have h1 : Filter.Tendsto
        (fun N : ℕ => (1 - (W (a-ε)/W a) ^ N) / (1 - W (a-ε)/W a))
        Filter.atTop (𝓝 ((1 - 0) / (1 - W (a-ε)/W a))) :=
      (tendsto_const_nhds.sub hpow).div tendsto_const_nhds hne
    have h2 : Filter.Tendsto (fun _ : ℕ => ε * (W (a-ε)/W a)) Filter.atTop
        (𝓝 (ε * (W (a-ε)/W a))) := tendsto_const_nhds
    have hbase2 : Filter.Tendsto
        (fun N : ℕ => ε * (W (a-ε)/W a) * ((1 - (W (a-ε)/W a) ^ N) / (1 - W (a-ε)/W a)))
        Filter.atTop (𝓝 (ε * (W (a-ε)/W a) / (1 - W (a-ε)/W a))) := by
      simpa only [sub_zero, mul_one_div] using h2.mul h1
    have hfun : (fun N : ℕ => ∑ k ∈ Finset.range N, ε * (W (a-ε)/W a) ^ (k+1))
        = (fun N : ℕ => ε * (W (a-ε)/W a) * ((1 - (W (a-ε)/W a) ^ N) / (1 - W (a-ε)/W a))) :=
      funext (fun N => hclosed N)
    rw [hfun]
    exact hbase2
  have hbridge : ∀ N : ℕ, ENNReal.ofReal (∑ k ∈ Finset.range N, ε * (W (a-ε)/W a) ^ (k+1))
      = ∑ k ∈ Finset.range N, ENNReal.ofReal ε * (ENNReal.ofReal (W (a-ε)/W a)) ^ (k+1) := by
    intro N
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun k _ => mul_nonneg hε0.le (pow_nonneg hr0 _))]
    apply Finset.sum_congr rfl
    intro k _
    rw [ENNReal.ofReal_mul hε0.le, ENNReal.ofReal_pow hr0]
  have hlimE : Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N, ENNReal.ofReal ε * (ENNReal.ofReal (W (a-ε)/W a)) ^ (k+1))
      Filter.atTop (𝓝 (ENNReal.ofReal (ε * (W (a-ε)/W a) / (1 - W (a-ε)/W a)))) := by
    have hcont : Filter.Tendsto
        (fun N : ℕ => ENNReal.ofReal (∑ k ∈ Finset.range N, ε * (W (a-ε)/W a) ^ (k+1)))
        Filter.atTop (𝓝 (ENNReal.ofReal (ε * (W (a-ε)/W a) / (1 - W (a-ε)/W a)))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hlimR
    simpa only [hbridge] using hcont
  exact le_of_tendsto hlimE (Filter.Eventually.of_forall (fun N => hfin N ε hε0 hεa))
