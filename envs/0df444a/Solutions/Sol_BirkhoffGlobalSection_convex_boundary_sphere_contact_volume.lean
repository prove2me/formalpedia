-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_boundary_sphere_contact_volume
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T20:13:26.78286+00:00
-- url     : https://prove2.me/submissions/9037c060-6e55-4232-b2f5-1f903b100b22

import Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_chart
import Theorems.Thm_BirkhoffGlobalSection_gauge_inverse_contact_weight
import Theorems.Thm_BirkhoffGlobalSection_weighted_sphere_contact_geometry

open scoped ContDiff Topology
open BirkhoffGlobalSection Set

theorem solution (B : Set Phase) (hc : Convex ℝ B)
    (h0 : B ∈ 𝓝 (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ B) (F : Phase → ℝ)
    (hzero : ∀ y ∈ frontier B, F y = 0)
    (hsmooth : ∀ y ∈ frontier B, ContDiffAt ℝ ∞ F y)
    (hrad : ∀ y ∈ frontier B, fderiv ℝ F y y ≠ 0)
    (u : Phase) (hu : u ∈ unitThreeSphere) :
    let G : Phase → Phase := fun x => (gauge B x)⁻¹ • x
    let f : Phase → ℝ := fun x => zNormSq (G x) + wNormSq (G x)
    let d : Phase → Phase → ℝ := fun v w =>
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
        fderiv ℝ (fun x => f x * phaseRadialContact x v) u w
    ∃ r v w : Phase,
      (u 0 * r 0 + u 1 * r 1 + u 2 * r 2 + u 3 * r 3 = 0) ∧
      (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) ∧
      (u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0) ∧
      0 < f u * phaseRadialContact u r * d v w -
        f u * phaseRadialContact u v * d r w +
        f u * phaseRadialContact u w * d r v := by
  have hG := ((smooth_radial_gauge_chart B hc h0 hb F hzero hsmooth hrad).2 u hu).1
  have h := gauge_inverse_contact_weight B h0 hb u hu hG
  exact (weighted_sphere_contact_geometry _ u hu h.1
    (h.2.1.differentiableAt (by simp))).2
