-- Prove2me | solution 1 for BirkhoffGlobalSection.gauge_inverse_scale_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:39:26.595262+00:00
-- url     : https://prove2.me/submissions/f9cc49ea-c382-4cfb-a748-d61a3a3fdcb1

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative
import Theorems.Thm_BirkhoffGlobalSection_radial_rescaling_contact_pullback
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization
import Theorems.Thm_BirkhoffGlobalSection_smooth_radial_gauge_chart

open BirkhoffGlobalSection
open scoped ContDiff Topology



set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution (B : Set Phase) (u : Phase)
    (hu : u ≠ 0) (hG : DifferentiableAt ℝ (fun x : Phase => (gauge B x)⁻¹ • x) u) :
    DifferentiableAt ℝ (fun x : Phase => (gauge B x)⁻¹) u := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, u i ≠ 0 := by
    by_contra! h
    exact hu (funext h)
  let G : Phase → Phase := fun x => (gauge B x)⁻¹ • x
  have hdcomp : DifferentiableAt ℝ (fun x => G x i) u := differentiableAt_pi.mp hG i
  have hdcoord : DifferentiableAt ℝ (fun x : Phase => x i) u :=
    (hasFDerivAt_apply i u).differentiableAt
  have hratio : DifferentiableAt ℝ (fun x => G x i / x i) u := by
    convert! hdcomp.mul (hdcoord.inv hi) using 1
  have hne : ∀ᶠ x in nhds u, x i ≠ 0 :=
    hdcoord.continuousAt.eventually (isOpen_compl_singleton.mem_nhds hi)
  have heq : (fun x : Phase => (gauge B x)⁻¹) =ᶠ[nhds u] (fun x => G x i / x i) := by
    filter_upwards [hne] with x hx
    simp [G, hx]
  exact hratio.congr_of_eventuallyEq heq
