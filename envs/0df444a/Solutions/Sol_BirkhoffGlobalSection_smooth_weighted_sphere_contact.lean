-- Prove2me | solution 1 for BirkhoffGlobalSection.smooth_weighted_sphere_contact
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:19:30.483314+00:00
-- url     : https://prove2.me/submissions/3e6f7f81-6900-4cc2-9893-ef115cfd0702

import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative

import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_nondegenerate
open scoped ContDiff Topology
open BirkhoffGlobalSection Set


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) :
    (∃ r : Phase,
      u 0 * r 0 + u 1 * r 1 + u 2 * r 2 + u 3 * r 3 = 0 ∧
      f u * phaseRadialContact u r ≠ 0) ∧
    (DifferentiableAt ℝ f u → ∀ v : Phase,
      u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0 →
      f u * phaseRadialContact u v = 0 →
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        f u * phaseRadialContact u w = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
          fderiv ℝ (fun x => f x * phaseRadialContact x v) u w = 0) → v = 0) := by
  obtain ⟨h1, h2⟩ := BirkhoffGlobalSection.weighted_radial_contact_nondegenerate u hu (f u) hf
    (fun v => fderiv ℝ f u v)
  refine ⟨h1, fun hd v hv hcv hw => h2 v hv hcv (fun w hw1 hw2 => ?_)⟩
  have := hw w hw1 hw2
  rw [BirkhoffGlobalSection.weighted_radial_contact_exterior_derivative f u v w hd] at this
  exact this
