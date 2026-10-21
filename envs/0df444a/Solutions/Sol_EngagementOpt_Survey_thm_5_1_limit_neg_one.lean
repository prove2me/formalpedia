-- Prove2me | solution 1 for EngagementOpt.Survey.thm_5_1_limit_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:38:04.489427+00:00
-- url     : https://prove2.me/submissions/98000f8b-87a7-41c9-9ac5-f5e0f36a8725

import Mathlib
import Definitions.Def_EngagementOpt_Survey_phi

set_option autoImplicit false
open Filter Topology EngagementOpt.Survey

theorem solution : Tendsto phi (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
  -- phi x = (x+1)/x - (x+1) log (x+1) / x^2, continuous at -1 with value 0
  let g : ℝ → ℝ := fun x => (x + 1) / x - (x + 1) * Real.log (x + 1) / x ^ 2
  have hcont : ContinuousAt g (-1) := by
    have h1 : ContinuousAt (fun x : ℝ => (x + 1) / x) (-1) :=
      ContinuousAt.div (by fun_prop) continuousAt_id (by norm_num)
    have h2 : ContinuousAt (fun x : ℝ => (x + 1) * Real.log (x + 1)) (-1) :=
      (Real.continuous_mul_log.comp (continuous_id.add continuous_const)).continuousAt
    have h3 : ContinuousAt (fun x : ℝ => (x + 1) * Real.log (x + 1) / x ^ 2) (-1) :=
      ContinuousAt.div h2 (by fun_prop) (by norm_num)
    exact h1.sub h3
  have hg : g (-1) = 0 := by simp [g]
  have ht : Tendsto g (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
    have := hcont.tendsto
    rw [hg] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  have hne : ∀ᶠ x : ℝ in 𝓝[>] (-1 : ℝ), x < 0 := by
    have : ∀ᶠ x : ℝ in 𝓝 (-1 : ℝ), x < 0 := Iio_mem_nhds (by norm_num)
    exact nhdsWithin_le_nhds this
  filter_upwards [hne] with x hx
  have hx0 : x ≠ 0 := hx.ne
  simp only [g, phi]
  field_simp
