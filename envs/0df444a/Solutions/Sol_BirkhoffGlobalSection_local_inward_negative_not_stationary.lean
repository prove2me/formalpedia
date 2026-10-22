-- Prove2me | solution 1 for BirkhoffGlobalSection.local_inward_negative_not_stationary
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:39:28.049979+00:00
-- url     : https://prove2.me/submissions/61ab00ab-2e20-4e10-b216-b757e4261dc8

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative
import Theorems.Thm_BirkhoffGlobalSection_radial_rescaling_contact_pullback
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization
import Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_chart
import Theorems.Thm_ConvexAnalysis_radial_derivative_pos_of_inward_negative
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false




set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution (f : ℝ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hc : ContinuousAt f 1) (hzero : f 1 = 0)
    (hneg : ∀ t : ℝ, 1 - ε ≤ t → t < 1 → f t < 0)
    (hsecond : 0 < deriv (deriv f) 1) : deriv f 1 ≠ 0 := by
  intro hstationary
  have hmin := isLocalMin_of_deriv_deriv_pos hsecond hstationary hc
  obtain ⟨η, hη, hnear⟩ := Metric.eventually_nhds_iff.mp hmin
  let δ : ℝ := min (η / 2) (ε / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ ≤ ε / 2 := min_le_right _ _
  have hδη : δ < η := (min_le_left _ _).trans_lt (by linarith)
  have hd : dist (1 - δ) (1 : ℝ) < η := by
    rw [Real.dist_eq]
    have heq : (1 - δ) - 1 = -δ := by ring
    rw [heq, abs_neg, abs_of_pos hδ]
    exact hδη
  have hl := hnear hd
  have hn := hneg (1 - δ) (by linarith) (by linarith)
  rw [hzero] at hl
  linarith
