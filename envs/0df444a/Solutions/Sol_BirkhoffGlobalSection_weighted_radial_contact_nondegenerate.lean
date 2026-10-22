-- Prove2me | solution 1 for BirkhoffGlobalSection.weighted_radial_contact_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:08:20.004112+00:00
-- url     : https://prove2.me/submissions/5a9e5223-1657-45a3-a930-b940d7f4a73f

import Theorems.Thm_BirkhoffGlobalSection_weighted_radial_contact_exterior_derivative

open scoped ContDiff Topology
open BirkhoffGlobalSection Set


set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution (u : Phase) (hu : u ∈ unitThreeSphere)
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
