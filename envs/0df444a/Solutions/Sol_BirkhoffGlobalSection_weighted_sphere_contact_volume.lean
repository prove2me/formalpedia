-- Prove2me | solution 1 for BirkhoffGlobalSection.weighted_sphere_contact_volume
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:08:21.359869+00:00
-- url     : https://prove2.me/submissions/a494684c-c39e-44d9-b928-6b7b7101cc9a

import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative

open scoped ContDiff Topology
open BirkhoffGlobalSection Set


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u) :
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
  dsimp only
  let r : Phase := ![u 2, u 3, -u 0, -u 1]
  let v : Phase := ![-u 1, u 0, u 3, -u 2]
  let w : Phase := ![u 3, -u 2, u 1, -u 0]
  have hQ : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = 1 := by
    simpa [zNormSq, wNormSq, add_assoc] using (show zNormSq u + wNormSq u = 1 from hu)
  have hr : phaseRadialContact u r = 1 / 2 := by
    simp [r, phaseRadialContact, phaseSymplecticForm]
    nlinarith [hQ]
  have hv : phaseRadialContact u v = 0 := by
    simp [v, phaseRadialContact, phaseSymplecticForm]
    ring
  have hw : phaseRadialContact u w = 0 := by
    simp [w, phaseRadialContact, phaseSymplecticForm]
    ring
  have hω : phaseSymplecticForm v w = -1 := by
    simp [v, w, phaseSymplecticForm]
    nlinarith [hQ]
  refine ⟨r, v, w, ?_, ?_, ?_, ?_⟩
  · simp [r]; ring
  · simp [v]; ring
  · simp [w]; ring
  · rw [hr, hv, hw]
    simp only [mul_zero, zero_mul, sub_zero, add_zero]
    rw [weighted_radial_contact_exterior_derivative f u v w hdf, hv, hw, hω]
    simp only [mul_zero, sub_self, mul_neg, mul_one, sub_neg_eq_add, zero_add]
    exact mul_pos (mul_pos hf (by norm_num)) hf
