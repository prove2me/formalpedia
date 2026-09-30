-- Prove2me | solution 1 for ConvexAnalysis.positive_hessian_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T00:11:38.264276+00:00
-- url     : https://prove2.me/submissions/ad2a8058-11b9-4fcf-aa30-68c2b20e784b

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
open NormedSpace
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem canonical_hessian_apply_eq (F : E → ℝ) (x v : E) (hc : ContDiffAt ℝ 2 F x) :
    fderiv ℝ (fun z => fderiv ℝ F z v) x v = fderiv ℝ (fderiv ℝ F) x v v := by
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  rw [fderiv_clm_apply hD (differentiableAt_const v)]
  simp

theorem solution (F : E → ℝ) (s : E)
    (hc : ContDiffAt ℝ 2 F s)
    (hpos : ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fun z => fderiv ℝ F z v) s v) :
    ∃ r > 0, ∀ x ∈ Metric.ball s r, ContDiffAt ℝ 2 F x ∧
      ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fun z => fderiv ℝ F z v) x v := by
  let H := fun x => fderiv ℝ (fderiv ℝ F) x
  have hHc : ContinuousAt H s :=
    (hc.fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv (by norm_num)
  let T : Set E := {v | ‖v‖ = 1}
  have hT : IsCompact T := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : E) 1
  have hunit : ∀ v ∈ T, 0 < H s v v := by
    intro v hv
    have hvne : v ≠ 0 := by intro he; have hh : ‖v‖ = 1 := hv; norm_num [he] at hh
    rw [← canonical_hessian_apply_eq F s v hc]
    exact hpos v hvne
  have hev : ∀ᶠ x in nhds s, ∀ v ∈ T, 0 < H x v v := by
    apply hT.eventually_forall_of_forall_eventually
    intro v hv
    have hHp : ContinuousAt (fun p : E × E => H p.1) (s, v) := hHc.comp continuousAt_fst
    have hQp : ContinuousAt (fun p : E × E => H p.1 p.2 p.2) (s, v) :=
      (hHp.clm_apply continuousAt_snd).clm_apply continuousAt_snd
    exact hQp.preimage_mem_nhds (Ioi_mem_nhds (hunit v hv))
  have hall : ∀ᶠ x in nhds s, ContDiffAt ℝ 2 F x ∧
      ∀ v : E, v ≠ 0 → 0 < fderiv ℝ (fun z => fderiv ℝ F z v) x v := by
    filter_upwards [hc.eventually (by norm_num), hev] with x hx hxu
    refine ⟨hx, ?_⟩
    intro v hv
    have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : normalize v ∈ T := norm_normalize hv
    have hscale (a : ℝ) (u : E) : H x (a • u) (a • u) = a ^ 2 * H x u u := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    have hrepr : H x v v = ‖v‖ ^ 2 * H x (normalize v) (normalize v) := by
      simpa only [norm_smul_normalize] using hscale ‖v‖ (normalize v)
    rw [canonical_hessian_apply_eq F x v hx, hrepr]
    exact mul_pos (sq_pos_of_pos hnorm) (hxu _ hu)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  exact ⟨r, hr, hball⟩
