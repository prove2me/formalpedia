-- Prove2me | solution 1 for ContinuousMapCalculus.hasFDerivAt_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T09:08:36.538479+00:00
-- url     : https://prove2.me/submissions/97908da7-7430-441c-8191-d871c92e86fb

import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

open Set Filter
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ContinuousMapCalculus
variable {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem norm_eval_comp_le (A : E →L[ℝ] C(K,F)) (k : K) :
    ‖(ContinuousMap.evalCLM ℝ k).comp A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact (A v).norm_coe_le_norm k |>.trans (A.le_opNorm v)


end ContinuousMapCalculus
open ContinuousMapCalculus

theorem solution {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → C(K,F)) (g : E → E →L[ℝ] C(K,F)) (x : E)
    (hg : ContinuousAt g x)
    (hd : ∀ y k, HasFDerivAt (fun z => f z k)
      ((ContinuousMap.evalCLM ℝ k).comp (g y)) y) :
    HasFDerivAt f (g x) x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hnear : ∀ᶠ y in 𝓝 x, ‖g y - g x‖ < ε := by
    simpa only [dist_eq_norm] using hg.eventually (Metric.ball_mem_nhds (g x) hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro k
  have hb : ∀ z ∈ Metric.ball x δ,
      ‖(ContinuousMap.evalCLM ℝ k).comp (g z) -
        (ContinuousMap.evalCLM ℝ k).comp (g x)‖ ≤ ε := by
    intro z hz
    rw [← ContinuousLinearMap.comp_sub]
    exact (norm_eval_comp_le (g z - g x) k).trans (hball hz).le
  exact (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ => (hd z k).hasFDerivWithinAt) hb
    (Metric.mem_ball_self hδ) hy

