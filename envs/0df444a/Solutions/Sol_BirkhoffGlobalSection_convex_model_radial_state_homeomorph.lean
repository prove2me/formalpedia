-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_radial_state_homeomorph
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:39:27.445156+00:00
-- url     : https://prove2.me/submissions/e98919ef-7038-458f-b95d-91c74f2f8dc1

import Theorems.Thm_BirkhoffGlobalSection_convex_model_complete_normalized_flow_of_model_fields
import Theorems.Thm_BirkhoffGlobalSection_convex_model_sphere_reeb_transport_of_model_fields
import Theorems.Thm_BirkhoffGlobalSection_convex_model_smooth_radial_chart
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

open BirkhoffGlobalSection Set
open scoped Topology ContDiff


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {μ c : ℝ} (M : ConvexRegularizationModel μ c) :
    ∃ e : {u : Phase // u ∈ unitThreeSphere} ≃ₜ ConvexModelState M,
      (∀ u, (e u : Phase) = (gauge M.body (u : Phase))⁻¹ • (u : Phase)) ∧
      (∀ y, (e.symm y : Phase) = radialNormalize (y : Phase)) := by
  have hc := convex_model_smooth_radial_chart M
  let e : {u : Phase // u ∈ unitThreeSphere} ≃ₜ ConvexModelState M := {
    toFun := fun u => ⟨(gauge M.body (u : Phase))⁻¹ • (u : Phase), (hc.2 u u.property).2.1⟩
    invFun := fun y => ⟨radialNormalize (y : Phase), (hc.1 y y.property).2.1⟩
    left_inv := fun u => Subtype.ext ((hc.2 u u.property).2.2)
    right_inv := fun y => Subtype.ext ((hc.1 y y.property).2.2)
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply continuous_iff_continuousAt.mpr
      intro u
      exact (hc.2 u u.property).1.continuousAt.comp continuous_subtype_val.continuousAt
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply continuous_iff_continuousAt.mpr
      intro y
      exact (hc.1 y y.property).1.continuousAt.comp continuous_subtype_val.continuousAt }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩
