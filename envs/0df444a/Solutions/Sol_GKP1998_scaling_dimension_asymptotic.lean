-- Prove2me | solution 1 for GKP1998.scaling_dimension_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:34:19.878576+00:00
-- url     : https://prove2.me/submissions/a9efbda5-54e1-417c-9327-d824c7c3669e

import Mathlib
import Definitions.Def_GKP1998_Defs

open Filter Topology Asymptotics GKP1998 in
theorem solution (n : ℕ) (hn : 1 ≤ n) (N : ℝ) (hN : 0 < N) :
    Tendsto (fun gYM : ℝ =>
        scalingDimension (Real.sqrt (4 + 4 * n * gYM * Real.sqrt (2 * N)))
          / (2 * Real.sqrt (n * gYM * Real.sqrt (2 * N))))
      atTop (𝓝 1) := by
  set c : ℝ := (n : ℝ) * Real.sqrt (2 * N) with hc_def
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (2 * N) := Real.sqrt_pos.mpr (by linarith)
  have hc : 0 < c := mul_pos hn' hs
  -- t = 1/(c g) → 0
  have ht : Tendsto (fun g : ℝ => (c * g)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop hc tendsto_id)
  have hcont : Continuous (fun t : ℝ => Real.sqrt t + Real.sqrt (t + 1)) := by
    fun_prop
  have hlim : Tendsto (fun g : ℝ => Real.sqrt ((c * g)⁻¹) + Real.sqrt ((c * g)⁻¹ + 1))
      atTop (𝓝 1) := by
    have := (hcont.tendsto 0).comp ht
    have h1 : Real.sqrt 0 + Real.sqrt (0 + 1) = 1 := by simp
    rw [h1] at this
    exact this
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with g hg
  have hcg : 0 < c * g := mul_pos hc hg
  have e1 : (n : ℝ) * g * Real.sqrt (2 * N) = c * g := by rw [hc_def]; ring
  have e2 : 4 + 4 * (n : ℝ) * g * Real.sqrt (2 * N) = 4 * (c * g + 1) := by rw [hc_def]; ring
  simp only [scalingDimension]
  rw [e1, e2]
  have hsq : 0 < Real.sqrt (c * g) := Real.sqrt_pos.mpr hcg
  have h4 : Real.sqrt (4 * (c * g + 1)) = 2 * Real.sqrt (c * g + 1) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hinv : Real.sqrt ((c * g)⁻¹) = (Real.sqrt (c * g))⁻¹ := Real.sqrt_inv _
  have hdiv : Real.sqrt ((c * g)⁻¹ + 1) = Real.sqrt (c * g + 1) / Real.sqrt (c * g) := by
    rw [← Real.sqrt_div' _ hcg.le]
    congr 1
    field_simp
    ring
  rw [h4, hinv, hdiv]
  field_simp
