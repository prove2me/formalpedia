-- Prove2me | solution 1 for EngagementOpt.Survey.lemma_D_1_limit_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:38:05.716548+00:00
-- url     : https://prove2.me/submissions/cc80a534-9ae3-4476-a5dd-0f11b78bbc50

import Mathlib
import Definitions.Def_EngagementOpt_Survey_phi

set_option autoImplicit false
open Filter Topology EngagementOpt.Survey

theorem solution : Tendsto phi (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2)) := by
  -- phi x = (x+1) * ((x - log (x+1)) / x^2)
  have hq : Tendsto (fun x : ℝ => (x - Real.log (x + 1)) / x ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2)) := by
    have hf : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), HasDerivAt (fun x : ℝ => x - Real.log (x + 1)) (1 - 1 / (x + 1)) x := by
      have : ∀ᶠ x : ℝ in 𝓝 0, 0 < x + 1 := by
        have hc : ContinuousAt (fun x : ℝ => x + 1) 0 := by fun_prop
        exact hc.eventually (lt_mem_nhds (by norm_num))
      filter_upwards [nhdsWithin_le_nhds this] with x hx
      have h1 : HasDerivAt (fun x : ℝ => x + 1) 1 x := (hasDerivAt_id' x).add_const 1
      have h2 := h1.log hx.ne'
      exact (hasDerivAt_id' x).sub h2
    have hg : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      refine Filter.Eventually.of_forall fun x => ?_
      simpa using hasDerivAt_pow 2 x
    have hg' : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), 2 * x ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero two_ne_zero hx
    have hft : Tendsto (fun x : ℝ => x - Real.log (x + 1)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun x : ℝ => x - Real.log (x + 1)) 0 := by
        refine ContinuousAt.sub continuousAt_id (ContinuousAt.log (by fun_prop) (by norm_num))
      have := hc.tendsto
      simp only [zero_add, Real.log_one, sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hgt : Tendsto (fun x : ℝ => x ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun x : ℝ => x ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_pow 2 : Continuous fun x : ℝ => x ^ 2).tendsto 0
      exact this.mono_left nhdsWithin_le_nhds
    refine HasDerivAt.lhopital_zero_nhdsNE hf hg hg' hft hgt ?_
    have hc : ContinuousAt (fun x : ℝ => 1 / (2 * (x + 1))) 0 := by
      refine ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)
    have ht := hc.tendsto
    have ht' : Tendsto (fun x : ℝ => 1 / (2 * (x + 1))) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2)) := by
      have := ht.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
      simpa using this
    refine ht'.congr' ?_
    have : ∀ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), x ≠ 0 ∧ x + 1 ≠ 0 := by
      have h1 : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), x + 1 ≠ 0 := by
        have hc : ContinuousAt (fun x : ℝ => x + 1) 0 := by fun_prop
        exact hc.eventually (isOpen_ne.mem_nhds (by norm_num))
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1] with x hx h2
      exact ⟨hx, h2⟩
    filter_upwards [this] with x ⟨hx, hx1⟩
    field_simp
    ring
  have hp : Tendsto (fun x : ℝ => x + 1) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have : ContinuousAt (fun x : ℝ => x + 1) 0 := by fun_prop
    have := this.tendsto
    simp only [zero_add] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := hp.mul hq
  simp only [one_mul] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx : x ≠ 0 := hx
  simp only [phi]
  field_simp
