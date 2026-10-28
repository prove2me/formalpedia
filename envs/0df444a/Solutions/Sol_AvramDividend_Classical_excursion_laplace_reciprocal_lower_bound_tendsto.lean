-- Prove2me | solution 1 for AvramDividend.Classical.excursion_laplace_reciprocal_lower_bound_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:24:09.307984+00:00
-- url     : https://prove2.me/submissions/a5ee80ed-0f30-48e3-be57-ae00d8e3a241

import Mathlib
open Filter Topology
open scoped ENNReal
theorem solution
    (k : ℝ) (hk : 0 < k) (F : ℝ → ℝ)
    (hF0 : F 0 = k) (hFcont : ContinuousAt F 0) :
    Filter.Tendsto (fun s : ℝ => ENNReal.ofReal ((F s)⁻¹))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (k⁻¹))) := by
  have h : ContinuousAt (fun s => (F s)⁻¹) 0 := hFcont.inv₀ (by rw [hF0]; exact hk.ne')
  have h2 : Tendsto (fun s => (F s)⁻¹) (𝓝 (0:ℝ)) (𝓝 k⁻¹) := by
    have := h.tendsto; simpa [hF0] using this
  exact (ENNReal.continuous_ofReal.tendsto _).comp (h2.mono_left nhdsWithin_le_nhds)
