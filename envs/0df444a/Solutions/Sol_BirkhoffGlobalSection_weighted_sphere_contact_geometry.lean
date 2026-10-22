-- Prove2me | solution 1 for BirkhoffGlobalSection.weighted_sphere_contact_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T20:12:42.639864+00:00
-- url     : https://prove2.me/submissions/967f9df4-1bc9-486d-a6e3-82ef7874d57b

import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative

open scoped ContDiff Topology
open BirkhoffGlobalSection Set

private theorem weighted_radial_contact_nondegenerate (u : Phase) (hu : u ∈ unitThreeSphere)
    (f : ℝ) (hf : 0 < f) (L : Phase → ℝ) :
    (∃ r : Phase,
      u 0 * r 0 + u 1 * r 1 + u 2 * r 2 + u 3 * r 3 = 0 ∧
      f * phaseRadialContact u r ≠ 0) ∧
    (∀ v : Phase,
      u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0 →
      f * phaseRadialContact u v = 0 →
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        f * phaseRadialContact u w = 0 →
        L v * phaseRadialContact u w - L w * phaseRadialContact u v -
          f * phaseSymplecticForm v w = 0) → v = 0) := by
  have hQ : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = 1 := by
    simpa [zNormSq, wNormSq, add_assoc] using (show zNormSq u + wNormSq u = 1 from hu)
  constructor
  · refine ⟨![u 2, u 3, -u 0, -u 1], ?_, ?_⟩
    · simp
      ring
    · have hp : phaseRadialContact u ![u 2, u 3, -u 0, -u 1] = 1 / 2 := by
        simp [phaseRadialContact, phaseSymplecticForm]
        nlinarith [hQ]
      rw [hp]
      exact ne_of_gt (mul_pos hf (by norm_num))
  · intro v htv hav hkernel
    have hav0 : phaseRadialContact u v = 0 := (mul_eq_zero.mp hav).resolve_left hf.ne'
    let w : Phase := ![v 2, v 3, -v 0, -v 1]
    have htw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 := by
      simp [w, phaseRadialContact, phaseSymplecticForm] at hav0 ⊢
      linarith
    have haw : phaseRadialContact u w = 0 := by
      simp [w, phaseRadialContact, phaseSymplecticForm]
      linarith
    have hk := hkernel w htw (by rw [haw, mul_zero])
    rw [hav0, haw, mul_zero, mul_zero, sub_self, zero_sub] at hk
    have homega : phaseSymplecticForm v w = 0 := by
      exact (mul_eq_zero.mp (neg_eq_zero.mp hk)).resolve_left hf.ne'
    have hsum : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 0 := by
      simp [w, phaseSymplecticForm] at homega
      nlinarith [homega]
    have hv0 : v 0 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
    have hv1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 2), sq_nonneg (v 3)]
    have hv2 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 3)]
    have hv3 : v 3 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    funext i
    fin_cases i <;> assumption

private theorem smooth_weighted_sphere_contact (f : Phase → ℝ) (u : Phase)
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
  have h := weighted_radial_contact_nondegenerate u hu (f u) hf (fderiv ℝ f u)
  refine ⟨h.1, ?_⟩
  intro hdf v htv hav hk
  apply h.2 v htv hav
  intro w htw haw
  rw [← weighted_radial_contact_exterior_derivative f u v w hdf]
  exact hk w htw haw

private theorem weighted_sphere_contact_volume (f : Phase → ℝ) (u : Phase)
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

theorem solution (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u) :
    ((∃ r : Phase,
      u 0 * r 0 + u 1 * r 1 + u 2 * r 2 + u 3 * r 3 = 0 ∧
      f u * phaseRadialContact u r ≠ 0) ∧
    (∀ v : Phase,
      u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0 →
      f u * phaseRadialContact u v = 0 →
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        f u * phaseRadialContact u w = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
          fderiv ℝ (fun x => f x * phaseRadialContact x v) u w = 0) → v = 0)) ∧
    (let d : Phase → Phase → ℝ := fun v w =>
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u v -
        fderiv ℝ (fun x => f x * phaseRadialContact x v) u w
    ∃ r v w : Phase,
      (u 0 * r 0 + u 1 * r 1 + u 2 * r 2 + u 3 * r 3 = 0) ∧
      (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 = 0) ∧
      (u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0) ∧
      0 < f u * phaseRadialContact u r * d v w -
        f u * phaseRadialContact u v * d r w +
        f u * phaseRadialContact u w * d r v) := by
  have h := smooth_weighted_sphere_contact f u hu hf
  exact ⟨⟨h.1, h.2 hdf⟩, weighted_sphere_contact_volume f u hu hf hdf⟩
