-- Prove2me | solution 1 for ConvexAnalysis.local_convex_sublevel_of_positive_tangential_hessian
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T00:13:48.949199+00:00
-- url     : https://prove2.me/submissions/ba3b14fe-79b6-464e-ba18-1ff389482fa4

import Mathlib.Tactic.Abel
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Theorems.Thm_ConvexAnalysis_quadratic_rank_one_correction
import Theorems.Thm_ConvexAnalysis_positive_hessian_neighborhood
import Theorems.Thm_ConvexAnalysis_convexOn_of_nonnegative_directional_hessian

open NormedSpace
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem tangential_hessian_rank_one_correction (F : E → ℝ) (s : E)
    (hc : ContDiffAt ℝ 2 F s)
    (htan : ∀ v : E, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : E, v ≠ 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v + c * (fderiv ℝ F s v) ^ 2 := by
  let H := fderiv ℝ (fderiv ℝ F) s
  let q : E → ℝ := fun v => H v v
  have hD : DifferentiableAt ℝ (fderiv ℝ F) s :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hq : Continuous q := H.continuous.clm_apply continuous_id
  have hhom : ∀ r : ℝ, ∀ v : E, q (r • v) = r ^ 2 * q v := by
    intro r v
    simp only [q, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hessian_eq (v : E) :
      fderiv ℝ (fun x => fderiv ℝ F x v) s v = q v := by
    rw [fderiv_clm_apply hD (differentiableAt_const v)]
    simp [q, H]
  have htanq : ∀ v : E, v ≠ 0 → fderiv ℝ F s v = 0 → 0 < q v := by
    intro v hv hLv
    rw [← hessian_eq]
    exact htan v hv hLv
  obtain ⟨c, hcpos, hpos⟩ := ConvexAnalysis.quadratic_rank_one_correction (fderiv ℝ F s) q hq hhom htanq
  refine ⟨c, hcpos, ?_⟩
  intro v hv
  rw [hessian_eq]
  exact hpos v hv

theorem corrected_defining_function_hessian_identity (F : E → ℝ) (s v : E) (c : ℝ)
    (hc : ContDiffAt ℝ 2 F s) (hzero : F s = 0) :
    let G : E → ℝ := fun x => F x + c * (F x * F x)
    fderiv ℝ (fun x => fderiv ℝ G x v) s v =
      fderiv ℝ (fun x => fderiv ℝ F x v) s v + 2 * c * (fderiv ℝ F s v) ^ 2 := by
  let G : E → ℝ := fun x => F x + c * (F x * F x)
  change fderiv ℝ (fun x => fderiv ℝ G x v) s v =
    fderiv ℝ (fun x => fderiv ℝ F x v) s v + 2 * c * (fderiv ℝ F s v) ^ 2
  let D : E → ℝ := fun x => fderiv ℝ F x v
  have hfirst (x : E) (hx : DifferentiableAt ℝ F x) :
      fderiv ℝ G x v = D x + c * (F x * D x + F x * D x) := by
    have hh := hx.hasFDerivAt.add ((hx.hasFDerivAt.mul hx.hasFDerivAt).const_mul c)
    have hh' : fderiv ℝ G x = fderiv ℝ F x +
        c • (F x • fderiv ℝ F x + F x • fderiv ℝ F x) := hh.fderiv
    rw [hh']
    simp [D, smul_eq_mul]
    ring
  have hDc : ContDiffAt ℝ 1 D s :=
    (hc.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hD := hDc.differentiableAt_one.hasFDerivAt
  have hF := (hc.differentiableAt (by norm_num)).hasFDerivAt
  let g : E → ℝ := fun x => D x + c * (F x * D x + F x * D x)
  have hg := hD.add (((hF.mul hD).add (hF.mul hD)).const_mul c)
  have heq : (fun x => fderiv ℝ G x v) =ᶠ[nhds s] g := by
    filter_upwards [hc.eventually (by norm_num)] with x hx
    exact hfirst x (hx.differentiableAt (by norm_num))
  have hG := hg.congr_of_eventuallyEq heq
  rw [hG.fderiv]
  simp only [smul_eq_mul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    hzero, zero_mul, zero_add, D]
  ring




open scoped Topology

theorem solution (F : E → ℝ) (s : E)
    (hc : ContDiffAt ℝ 2 F s) (hz : F s = 0)
    (htan : ∀ v : E, v ≠ 0 → fderiv ℝ F s v = 0 →
      0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v) :
    ∃ U : Set E, U ∈ nhds s ∧ Convex ℝ ({y | F y ≤ 0} ∩ U) := by
  obtain ⟨c, hcp, hpos⟩ := tangential_hessian_rank_one_correction F s hc htan
  let k := c / 2
  let G : E → ℝ := fun x => F x + k * (F x * F x)
  have hcG : ContDiffAt ℝ 2 G s := hc.add (contDiffAt_const.mul (hc.mul hc))
  have hGpos : ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fun x => fderiv ℝ G x v) s v := by
    intro v hv
    rw [corrected_defining_function_hessian_identity F s v k hc hz]
    have hk : 2 * k = c := by dsimp [k]; ring
    rw [hk]
    exact hpos v hv
  obtain ⟨r, hr, hball⟩ := ConvexAnalysis.positive_hessian_neighborhood G s hcG hGpos
  have hcoeff : ∀ᶠ y in nhds s, 0 < 1 + k * F y := by
    have hcon : ContinuousAt (fun y => 1 + k * F y) s :=
      continuousAt_const.add (hc.continuousAt.const_mul k)
    exact hcon.preimage_mem_nhds (Ioi_mem_nhds (by simp [hz]))
  obtain ⟨r', hr', hball'⟩ := Metric.mem_nhds_iff.mp hcoeff
  let R := min r r'
  have hR : 0 < R := lt_min hr hr'
  have hsub : Metric.ball s R ⊆ Metric.ball s r := Metric.ball_subset_ball (min_le_left _ _)
  have hsub' : Metric.ball s R ⊆ Metric.ball s r' := Metric.ball_subset_ball (min_le_right _ _)
  have hconv : ConvexOn ℝ (Metric.ball s R) G :=
    ConvexAnalysis.convexOn_of_nonnegative_directional_hessian G _ (convex_ball s R)
      (fun y hy => (hball y (hsub hy)).1)
      (fun y hy v => by
        by_cases hv : v = 0
        · simp [hv]
        · exact le_of_lt ((hball y (hsub hy)).2 v hv))
  refine ⟨Metric.ball s R, Metric.ball_mem_nhds s hR, ?_⟩
  have heq : {y | F y ≤ 0} ∩ Metric.ball s R = {y ∈ Metric.ball s R | G y ≤ 0} := by
    ext y
    constructor
    · rintro ⟨hyF, hy⟩
      refine ⟨hy, ?_⟩
      have hp := hball' (hsub' hy)
      have he : G y = F y * (1 + k * F y) := by dsimp [G]; ring
      rw [he]
      exact mul_nonpos_of_nonpos_of_nonneg hyF hp.le
    · rintro ⟨hy, hyG⟩
      refine ⟨?_, hy⟩
      have hp := hball' (hsub' hy)
      have he : G y = F y * (1 + k * F y) := by dsimp [G]; ring
      rw [he] at hyG
      by_contra hn
      exact (not_lt_of_ge hyG) (mul_pos (lt_of_not_ge hn) hp)
  rw [heq]
  exact hconv.convex_le 0
