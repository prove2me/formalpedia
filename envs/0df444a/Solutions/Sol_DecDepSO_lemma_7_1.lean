-- Prove2me | solution 1 for DecDepSO.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:18:38.586505+00:00
-- url     : https://prove2.me/submissions/34442f39-f6d6-48cb-a4c7-117a1b8ca86a

import Mathlib
import Definitions.Def_DecDepSO_Assumption7ab

set_option autoImplicit false

open Filter Topology

namespace DecDepSO.Lemma71Proof

/-- First-order inequality for an `α`-strongly convex differentiable function. -/
theorem first_order {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {α : ℝ} (hsc : StrongConvexOn Set.univ α f) (hd : Differentiable ℝ f)
    (x y : E) :
    fderiv ℝ f x (y - x) ≤ f y - f x - α / 2 * ‖x - y‖ ^ 2 := by
  set φ : ℝ → ℝ := fun t => f (x + t • (y - x)) with hφdef
  have hline : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hφ : HasDerivAt φ (fderiv ℝ f x (y - x)) 0 := by
    have h1 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (y - x)) := by
      simpa using (hd x).hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℝ) hline
  have hslope := hφ.tendsto_slope_zero_right
  have hrhs : Tendsto (fun t : ℝ => f y - f x - (1 - t) * (α / 2 * ‖x - y‖ ^ 2)) (𝓝[>] 0)
      (𝓝 (f y - f x - α / 2 * ‖x - y‖ ^ 2)) := by
    have hc : Continuous (fun t : ℝ => f y - f x - (1 - t) * (α / 2 * ‖x - y‖ ^ 2)) := by
      fun_prop
    have h2 := hc.tendsto 0
    simp only [sub_zero, one_mul] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hslope hrhs
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hconv := hsc.2 (Set.mem_univ x) (Set.mem_univ y) (show 0 ≤ 1 - t by linarith) ht0.le
    (by ring)
  have heq : (1 - t) • x + t • y = x + t • (y - x) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [heq, smul_eq_mul, smul_eq_mul] at hconv
  simp only [hφdef, zero_add, zero_smul, add_zero, smul_eq_mul]
  rw [inv_mul_le_iff₀ ht0]
  nlinarith [hconv]

end DecDepSO.Lemma71Proof

open DecDepSO DecDepSO.Lemma71Proof in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} {D : Set E} {r : E → ℝ} {L B α : ℝ} {xbar : E}
    (hA : Assumption7ab f D r L B α xbar) (x v : E)
    (hv : ‖v - gradient f x‖ ≤ B * ‖x - xbar‖) :
    f xbar ≥ f x + inner ℝ v (xbar - x) + α * (1 - 2 * (B / α)) / 2 * ‖x - xbar‖ ^ 2 := by
  have hα := hA.α_pos
  have h1 := first_order hA.strongConvex hA.differentiable x xbar
  have hg : inner ℝ (gradient f x) (xbar - x) = fderiv ℝ f x (xbar - x) := by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  have hcs : inner ℝ (v - gradient f x) (xbar - x) ≤ B * ‖x - xbar‖ ^ 2 := by
    calc inner ℝ (v - gradient f x) (xbar - x)
        ≤ ‖v - gradient f x‖ * ‖xbar - x‖ := real_inner_le_norm _ _
      _ ≤ B * ‖x - xbar‖ * ‖x - xbar‖ := by
        rw [norm_sub_rev xbar x]
        exact mul_le_mul_of_nonneg_right hv (norm_nonneg _)
      _ = B * ‖x - xbar‖ ^ 2 := by ring
  rw [inner_sub_left, hg] at hcs
  have hcoef : α * (1 - 2 * (B / α)) / 2 = α / 2 - B := by
    field_simp
  rw [hcoef]
  nlinarith [hcs, h1]
