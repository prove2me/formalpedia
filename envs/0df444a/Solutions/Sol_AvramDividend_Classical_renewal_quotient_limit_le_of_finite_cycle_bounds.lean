-- Prove2me | solution 1 for AvramDividend.Classical.renewal_quotient_limit_le_of_finite_cycle_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:06:50.788015+00:00
-- url     : https://prove2.me/submissions/77e5f458-1917-4424-8266-6587c92ba97e

import Mathlib
import Theorems.Thm_avram_dividend_classical_renewal_quotient_limit_le_pointwise_upper_bound_fa7e49e3
import Theorems.Thm_avram_dividend_classical_renewal_quotient_limit_le_identity_27bb7271
import Theorems.Thm_avram_dividend_classical_renewal_quotient_limit_le_identity_4dff457e

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal

-- Parent assembly over three Proved wave helpers (pointwise bound,
-- punctured-neighbourhood argument, slope funext identity).

theorem solution (V : ℝ≥0∞) (W : ℝ → ℝ) (a d : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W d a) (hd : d ≠ 0)
    (hWa : 0 < W a)
    (hW8 : ∀ ε : ℝ, 0 < ε → ε < a → 0 ≤ W (a - ε))
    (hlt : ∀ ε : ℝ, 0 < ε → ε < a → W (a - ε) < W a)
    (hfin : ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < a →
      ∑ k ∈ Finset.range N,
        ENNReal.ofReal ε * (ENNReal.ofReal (W (a - ε) / W a)) ^ (k + 1) ≤ V) :
    ENNReal.ofReal (W a / d) ≤ V := by
  have hWa0 : W a ≠ 0 := ne_of_gt hWa
  -- Per-epsilon quotient bound (geometric argument).
  have step : ∀ ε : ℝ, 0 < ε → ε < a →
      ENNReal.ofReal (ε * (W (a - ε) / W a) / (1 - W (a - ε) / W a)) ≤ V := avram_dividend_classical_renewal_quotient_limit_le_pointwise_upper_bound_fa7e49e3 (V := V) (W := W) (a := a) (d := d) (ha := ha) (hD := hD) (hd := hd) (hWa := hWa) (hW8 := hW8) (hlt := hlt) (hfin := hfin) (hWa0 := hWa0)
  have hWcont : Filter.Tendsto (fun ε : ℝ => W (a - ε)) (𝓝[>] (0:ℝ)) (𝓝 (W a)) := by
    have hcont0 : Continuous (fun ε : ℝ => a - ε) := continuous_const.sub continuous_id
    have hsub : Filter.Tendsto (fun ε : ℝ => a - ε) (𝓝 (0:ℝ)) (𝓝 a) := by
      simpa only [sub_zero] using hcont0.tendsto (0 : ℝ)
    exact (hD.continuousAt.tendsto.comp (hsub.mono_left nhdsWithin_le_nhds))
  have hslope := hD.tendsto_slope
  have harg : Filter.Tendsto (fun ε : ℝ => a - ε) (𝓝[>] (0:ℝ)) (𝓝[≠] a) := avram_dividend_classical_renewal_quotient_limit_le_identity_27bb7271 (V := V) (W := W) (a := a) (d := d) (ha := ha) (hD := hD) (hd := hd) (hWa := hWa) (hW8 := hW8) (hlt := hlt) (hfin := hfin) (hWa0 := hWa0) (step := step) (hWcont := hWcont)
  have hgap0 : Filter.Tendsto ((slope W a) ∘ (fun ε : ℝ => a - ε)) (𝓝[>] (0:ℝ)) (𝓝 d) :=
    hslope.comp harg
  have hfun2 : ((slope W a) ∘ (fun ε : ℝ => a - ε))
      = (fun ε : ℝ => (W a - W (a - ε)) / ε) := avram_dividend_classical_renewal_quotient_limit_le_identity_4dff457e (V := V) (W := W) (a := a) (d := d) (ha := ha) (hD := hD) (hd := hd) (hWa := hWa) (hW8 := hW8) (hlt := hlt) (hfin := hfin) (hWa0 := hWa0) (step := step) (hWcont := hWcont) (harg := harg) (hgap0 := hgap0)
  have hgap : Filter.Tendsto (fun ε : ℝ => (W a - W (a - ε)) / ε) (𝓝[>] (0:ℝ)) (𝓝 d) := by
    rw [← hfun2]
    exact hgap0
  have hC : ∀ ε : ℝ, ε / (W a - W (a - ε)) = 1 / ((W a - W (a - ε)) / ε) := by
    intro ε
    by_cases hgapε : W a - W (a - ε) = 0
    · simp [hgapε, div_zero, zero_div]
    · by_cases hε : ε = 0
      · subst hε
        simp [div_zero, zero_div]
      · field_simp
  have h2 : Filter.Tendsto (fun ε : ℝ => 1 / ((W a - W (a - ε)) / ε)) (𝓝[>] (0:ℝ)) (𝓝 (1 / d)) :=
    tendsto_const_nhds.div hgap hd
  have hClim : Filter.Tendsto (fun ε : ℝ => ε / (W a - W (a - ε))) (𝓝[>] (0:ℝ)) (𝓝 (1 / d)) := by
    simpa only [← hC] using h2
  have heq : ∀ ε : ℝ, W (a - ε) * (ε / (W a - W (a - ε)))
      = ε * (W (a - ε) / W a) / (1 - W (a - ε) / W a) := by
    intro ε
    by_cases hgapε : W a - W (a - ε) = 0
    · have hWeq : W (a - ε) = W a := by linarith
      simp [hgapε, hWeq, div_zero, mul_zero, div_self hWa0]
    · field_simp
  have hlim : Filter.Tendsto
      (fun ε : ℝ => ε * (W (a - ε) / W a) / (1 - W (a - ε) / W a))
      (𝓝[>] (0:ℝ)) (𝓝 (W a / d)) := by
    have hmul := hWcont.mul hClim
    rw [mul_one_div] at hmul
    simpa only [heq] using hmul
  have hlimE : Filter.Tendsto
      (fun ε : ℝ => ENNReal.ofReal (ε * (W (a - ε) / W a) / (1 - W (a - ε) / W a)))
      (𝓝[>] (0:ℝ)) (𝓝 (ENNReal.ofReal (W a / d))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hlim
  apply le_of_tendsto hlimE
  filter_upwards [(eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with ε hεa hε
  have hε0 : (0:ℝ) < ε := hε
  exact step ε hε0 hεa
