-- Prove2me | solution 1 for AvramDividend.Classical.renewal_quotient_le_of_finite_cycle_bounds_of_pos_barrier
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:37:21.038261+00:00
-- url     : https://prove2.me/submissions/c25025e0-f401-49cf-a5f4-6b6ba6333e05

import Mathlib

open Filter Topology
open scoped ENNReal

theorem solution
    (V : ℝ≥0∞) (W : ℝ → ℝ) (a d : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W d a) (hd : d ≠ 0)
    (hWa : 0 < W a)
    (hW8 : ∀ ε : ℝ, 0 < ε → ε < a → 0 ≤ W (a - ε))
    (hlt : ∀ ε : ℝ, 0 < ε → ε < a → W (a - ε) < W a)
    (hfin : ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < a →
      ∑ k ∈ Finset.range N,
        ENNReal.ofReal ε * (ENNReal.ofReal (W (a - ε) / W a)) ^ (k + 1) ≤ V) :
    ENNReal.ofReal (W a / d) ≤ V := by
  set q : ℝ → ℝ := fun ε => W (a - ε) / W a with hq
  -- Step 1: the full geometric series is bounded by V
  have step1 : ∀ ε, 0 < ε → ε < a → ENNReal.ofReal (ε * q ε * (1 - q ε)⁻¹) ≤ V := by
    intro ε h1 h2
    have hq0 : 0 ≤ q ε := div_nonneg (hW8 ε h1 h2) hWa.le
    have hq1 : q ε < 1 := (div_lt_one hWa).2 (hlt ε h1 h2)
    have hs : HasSum (fun k : ℕ => ε * q ε * q ε ^ k) (ε * q ε * (1 - q ε)⁻¹) :=
      (hasSum_geometric_of_lt_one hq0 hq1).mul_left (ε * q ε)
    have hT := (ENNReal.continuous_ofReal.tendsto _).comp hs.tendsto_sum_nat
    refine le_of_tendsto' hT (fun N => ?_)
    have := hfin N ε h1 h2
    simp only [Function.comp]
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul h1.le, ENNReal.ofReal_pow hq0,
      pow_succ]
    ring
  -- Step 2: the limit as ε → 0⁺
  have hcont : Tendsto (fun ε : ℝ => a - ε) (𝓝[>] 0) (𝓝 a) := by
    have : Tendsto (fun ε : ℝ => a - ε) (𝓝 0) (𝓝 (a - 0)) :=
      tendsto_const_nhds.sub tendsto_id
    simpa using this.mono_left nhdsWithin_le_nhds
  have hqlim : Tendsto q (𝓝[>] 0) (𝓝 1) := by
    have := ((hD.continuousAt.tendsto).comp hcont).div_const (W a)
    rwa [div_self hWa.ne'] at this
  have hslope : Tendsto (fun ε : ℝ => (W a - W (a - ε)) / ε) (𝓝[>] 0) (𝓝 d) := by
    have h0 := (hasDerivAt_iff_tendsto_slope_zero.1 hD)
    have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun ε : ℝ => -ε) (𝓝 0) (𝓝 (-0)) := tendsto_id.neg
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact neg_ne_zero.2 (ne_of_gt hε)
    refine (h0.comp hneg).congr (fun ε => ?_)
    simp only [Function.comp, smul_eq_mul, ← sub_eq_add_neg]
    rw [inv_neg, div_eq_inv_mul]
    ring
  have hlim : Tendsto (fun ε => ε * q ε * (1 - q ε)⁻¹) (𝓝[>] 0) (𝓝 (W a / d)) := by
    have h3 := (hqlim.mul_const (W a)).mul (hslope.inv₀ hd)
    rw [one_mul, ← div_eq_mul_inv] at h3
    refine h3.congr (fun ε => ?_)
    have hA : W a ≠ 0 := hWa.ne'
    simp only [hq]
    rw [show 1 - W (a - ε) / W a = (W a - W (a - ε)) / W a by field_simp, inv_div, inv_div]
    ring
  -- Step 3
  refine le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp hlim) ?_
  filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
  exact step1 ε hε.1 hε.2
