-- Prove2me | solution 1 for Bl.general_b_fact_bis_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:27.880806+00:00
-- url     : https://prove2.me/submissions/a136267c-d46d-471d-81c2-cf67702e7e04

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactBisForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Bl Bl.general_b_fact_bis_form
namespace Bl.general_b_fact_bis_form
theorem _root_.solution :
  ∀ {F : Type u_1} [inst : NormedAddCommGroup.{u_1} F] [inst_1 : NormedSpace.{0, u_1} Complex F] {U : Set.{u_1} F},
  IsOpen.{u_1} U →
    ∀ {G : F → Complex},
      DifferentiableOn.{0, u_1, 0} Complex G U →
        ∀ {y : F} {R C : Real},
          LT.lt.{0} 0 R →
            LE.le.{u_1} (Metric.closedBall.{u_1} y R) U →
              (∀ (z : F),
                  Membership.mem.{u_1, u_1} (Metric.closedBall.{u_1} y R) z → LE.le.{0} (Norm.norm.{0} (G z)) C) →
                LE.le.{0} (Norm.norm.{u_1} (fderiv.{0, u_1, 0} Complex G y)) (HDiv.hDiv.{0, 0, 0} C R) := by
  intro F _ _ U hU G hG y R C hR hsub hC
  have hyU : y ∈ U := hsub (Metric.mem_closedBall_self hR.le)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC y (Metric.mem_closedBall_self hR.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hC0 hR.le) ?_
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set r : ℝ := R / ‖v‖ with hr_def
  have hr : 0 < r := div_pos hR hvpos
  have key : ∀ t : ℂ, ‖t‖ ≤ r → y + t • v ∈ Metric.closedBall y R := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    calc ‖t‖ * ‖v‖ ≤ r * ‖v‖ := by gcongr
      _ = R := div_mul_cancel₀ R hv'
  set g : ℂ → ℂ := G ∘ (fun t : ℂ => y + t • v) with hg_def
  have hl : ∀ t : ℂ, HasDerivAt (fun s : ℂ => y + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have hgd : DifferentiableOn ℂ g (Metric.closedBall (0 : ℂ) r) := by
    intro t ht
    have hmem : y + t • v ∈ U := hsub (key t (by simpa using ht))
    have hGt : DifferentiableAt ℂ G (y + t • v) := hG.differentiableAt (hU.mem_nhds hmem)
    exact (hGt.comp t (hl t).differentiableAt).differentiableWithinAt
  have hdc : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) hr.ne']
    exact hgd
  have hbd : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖g z‖ ≤ C := by
    intro z hz
    have hz' : ‖z‖ = r := by simpa using hz
    exact hC _ (key z hz'.le)
  have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc hbd
  have hGy : HasFDerivAt G (fderiv ℂ G y) y := (hG.differentiableAt (hU.mem_nhds hyU)).hasFDerivAt
  have hder : HasDerivAt g (fderiv ℂ G y v) 0 :=
    hGy.comp_hasDerivAt_of_eq (0 : ℂ) (hl 0) (by simp)
  rw [hder.deriv] at hest
  calc ‖fderiv ℂ G y v‖ ≤ C / r := hest
    _ = C / R * ‖v‖ := by rw [hr_def, div_div_eq_mul_div, mul_div_right_comm]
end Bl.general_b_fact_bis_form
