-- Prove2me | solution 1 for FriedCrossing.HQuot.hasDerivAt_hq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:03:21.236914+00:00
-- url     : https://prove2.me/submissions/f62cb97d-6dd6-4d7b-8c9a-04711cdc8d32

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_HQuot_taylor2

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.HQuot
namespace FriedCrossing.HQuot
theorem _root_.solution {f f' f'' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hc : ContinuousAt f'' 0) :
    HasDerivAt (hq f f') (hq' f f' f'' 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨δ, hδ, fun t ht hdist => ?_⟩
  have ht0 : t ≠ 0 := by simpa using ht
  obtain ⟨ξ, hξ, hR⟩ := taylor2 hf hf' ht0
  have hval : t⁻¹ • (hq f f' (0 + t) - hq f f' 0) = f'' ξ / 2 := by
    simp only [hq, zero_add, ht0, if_false, if_true, smul_eq_mul]
    have hft : f t - f 0 = t * f' 0 + t ^ 2 * f'' ξ / 2 := by linarith
    rw [hft]
    field_simp
    ring
  rw [hval]
  rw [Real.dist_eq, sub_zero] at hdist
  have hξδ : dist ξ 0 < δ := by rw [Real.dist_eq, sub_zero]; exact lt_trans hξ hdist
  have := hball hξδ
  rw [Real.dist_eq] at this
  simp only [hq', if_true]
  rw [Real.dist_eq]
  calc |f'' ξ / 2 - f'' 0 / 2| = |f'' ξ - f'' 0| / 2 := by rw [← sub_div, abs_div, abs_two]
    _ < ε := by linarith
end FriedCrossing.HQuot
