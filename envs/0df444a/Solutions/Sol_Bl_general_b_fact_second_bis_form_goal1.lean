-- Prove2me | solution 1 for Bl.general_b_fact_second_bis_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:09.580836+00:00
-- url     : https://prove2.me/submissions/3f53559c-77e9-40eb-8f48-aee242937e36

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.general_b_fact_second_bis_form
namespace Bl.general_b_fact_second_bis_form
theorem _root_.solution :
  ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Complex E]
  [inst_2 : NormedAddCommGroup.{u_2} F] [inst_3 : NormedSpace.{0, u_2} Complex F] {f : E → F} {y : E} {δ M : Real},
  LT.lt.{0} 0 δ →
    DifferentiableOn.{0, u_1, u_2} Complex f (Metric.ball.{u_1} y δ) →
      (∀ (z : E), Membership.mem.{u_1, u_1} (Metric.ball.{u_1} y δ) z → LE.le.{0} (Norm.norm.{u_2} (f z)) M) →
        LE.le.{0} (Norm.norm.{max u_2 u_1} (fderiv.{0, u_1, u_2} Complex f y)) (HDiv.hDiv.{0, 0, 0} M δ) := by
  intro E F _ _ _ _ f y δ M hδ hf hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y (Metric.mem_ball_self hδ))
  have hdy : DifferentiableAt ℂ f y :=
    hf.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hδ.le) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hline : ∀ t : ℂ, HasDerivAt (fun t : ℂ => y + t • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have hmaps : ∀ t : ℂ, ‖t‖ * ‖v‖ < δ → y + t • v ∈ Metric.ball y δ := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [norm_smul] using ht
  have hr : ∀ r : ℝ, 0 < r → r < δ → ‖fderiv ℂ f y v‖ * r ≤ M * ‖v‖ := by
    intro r hr0 hrδ
    have hgd : DifferentiableOn ℂ (fun t : ℂ => f (y + t • v)) (Metric.ball 0 (δ / ‖v‖)) := by
      intro t ht
      have ht' : ‖t‖ * ‖v‖ < δ := by
        rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hvpos] at ht
        exact ht
      exact ((hf.differentiableAt (Metric.isOpen_ball.mem_nhds (hmaps t ht'))).comp t
        (hline t).differentiableAt).differentiableWithinAt
    have hR : 0 < r / ‖v‖ := div_pos hr0 hvpos
    have hcl : DiffContOnCl ℂ (fun t : ℂ => f (y + t • v)) (Metric.ball 0 (r / ‖v‖)) := by
      refine DifferentiableOn.diffContOnCl (hgd.mono ?_)
      rw [closure_ball _ hR.ne']
      exact Metric.closedBall_subset_ball ((div_lt_div_iff_of_pos_right hvpos).2 hrδ)
    have hderiv : deriv (fun t : ℂ => f (y + t • v)) 0 = fderiv ℂ f y v := by
      have h := hdy.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) (hline 0) (by simp)
      exact h.deriv
    have hb : ∀ z ∈ Metric.sphere (0 : ℂ) (r / ‖v‖), ‖f (y + z • v)‖ ≤ M := by
      intro z hz
      apply hM
      apply hmaps
      rw [mem_sphere_zero_iff_norm] at hz
      rw [hz, div_mul_cancel₀ _ hvpos.ne']
      exact hrδ
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hcl hb
    rw [hderiv, div_div_eq_mul_div, le_div_iff₀ hr0] at h
    exact h
  have ht : Filter.Tendsto (fun r : ℝ => ‖fderiv ℂ f y v‖ * r) (nhdsWithin δ (Set.Iio δ))
      (nhds (‖fderiv ℂ f y v‖ * δ)) :=
    ((continuous_const.mul continuous_id).tendsto δ).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ r in nhdsWithin δ (Set.Iio δ), ‖fderiv ℂ f y v‖ * r ≤ M * ‖v‖ := by
    filter_upwards [Ioo_mem_nhdsLT hδ] with r h1 using hr r h1.1 h1.2
  have hlim := le_of_tendsto ht hev
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  exact hlim
end Bl.general_b_fact_second_bis_form
