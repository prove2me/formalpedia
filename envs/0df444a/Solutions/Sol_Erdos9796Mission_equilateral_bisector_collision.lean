-- Prove2me | solution 1 for Erdos9796Mission.equilateral_bisector_collision
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-12T23:18:25.20234+00:00
-- url     : https://prove2.me/submissions/955b0c78-aca6-457d-9e86-ae375fefcaf0

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Definitions.Def_Erdos9796Mission

open scoped EuclideanGeometry

namespace Erdos9796Mission.Internal

/- Squared distance in the plane, expanded in the two coordinates. -/
theorem dist_sq_coords (u v : Plane) :
    dist u v ^ 2 = (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

set_option maxHeartbeats 2000000 in
/- The proof eliminates one planar Gram determinant and two sums of squares. -/
theorem coordinate_collision
    {a₀ a₁ b₀ b₁ c₀ c₁ x₀ x₁ R S : ℝ}
    (hR : 0 < R)
    (haa : a₀ ^ 2 + a₁ ^ 2 = R)
    (hbb : b₀ ^ 2 + b₁ ^ 2 = R)
    (hcc : c₀ ^ 2 + c₁ ^ 2 = R)
    (hS : x₀ ^ 2 + x₁ ^ 2 = S)
    (hab : a₀ * b₀ + a₁ * b₁ = R / 2)
    (hax : a₀ * x₀ + a₁ * x₁ = S / 2)
    (hbx : b₀ * x₀ + b₁ * x₁ = S / 2)
    (hcxca :
      c₀ * x₀ + c₁ * x₁ - (c₀ * a₀ + c₁ * a₁) =
        (S - R) / 2) :
    (x₀ = 0 ∧ x₁ = 0) ∨ (c₀ = b₀ ∧ c₁ = b₁) := by
  have hgram :
      (a₀ ^ 2 + a₁ ^ 2) * (b₀ ^ 2 + b₁ ^ 2) * (x₀ ^ 2 + x₁ ^ 2)
        + 2 * (a₀ * b₀ + a₁ * b₁) * (a₀ * x₀ + a₁ * x₁)
          * (b₀ * x₀ + b₁ * x₁)
        - (a₀ ^ 2 + a₁ ^ 2) * (b₀ * x₀ + b₁ * x₁) ^ 2
        - (b₀ ^ 2 + b₁ ^ 2) * (a₀ * x₀ + a₁ * x₁) ^ 2
        - (x₀ ^ 2 + x₁ ^ 2) * (a₀ * b₀ + a₁ * b₁) ^ 2 = 0 := by
    ring
  rw [haa, hbb, hS, hab, hax, hbx] at hgram
  have hfactor : S * (3 * R - S) = 0 := by
    nlinarith only [hgram, hR]
  rcases mul_eq_zero.mp hfactor with hS₀ | hS₃
  · left
    constructor
    · nlinarith only [hS, hS₀, sq_nonneg x₀, sq_nonneg x₁]
    · nlinarith only [hS, hS₀, sq_nonneg x₀, sq_nonneg x₁]
  · right
    have hSeq : S = 3 * R := by nlinarith only [hS₃]
    have hxdiff :
        (x₀ - a₀ - b₀) ^ 2 + (x₁ - a₁ - b₁) ^ 2 = 0 := by
      nlinarith only [haa, hbb, hS, hSeq, hab, hax, hbx]
    have hx₀ : x₀ = a₀ + b₀ := by
      nlinarith only [hxdiff, sq_nonneg (x₀ - a₀ - b₀), sq_nonneg (x₁ - a₁ - b₁)]
    have hx₁ : x₁ = a₁ + b₁ := by
      nlinarith only [hxdiff, sq_nonneg (x₀ - a₀ - b₀), sq_nonneg (x₁ - a₁ - b₁)]
    have hcb : c₀ * b₀ + c₁ * b₁ = R := by
      rw [hx₀, hx₁, hSeq] at hcxca
      nlinarith only [hcxca]
    have hcbdiff : (c₀ - b₀) ^ 2 + (c₁ - b₁) ^ 2 = 0 := by
      nlinarith only [hcc, hbb, hcb]
    constructor
    · nlinarith only [hcbdiff, sq_nonneg (c₀ - b₀), sq_nonneg (c₁ - b₁)]
    · nlinarith only [hcbdiff, sq_nonneg (c₀ - b₀), sq_nonneg (c₁ - b₁)]

end Erdos9796Mission.Internal

set_option maxHeartbeats 5000000 in
/- If the six equilateral distances and the bisector equality hold, then
   either the two equilateral vertices agree or the third point is the common
   endpoint. -/
theorem solution
    {p a b c x : Erdos9796Mission.Plane} {r : ℝ} (hr : 0 < r)
    (hpa : dist p a = r) (hpb : dist p b = r) (hpc : dist p c = r)
    (hab : dist a b = r) (hax : dist a x = r) (hbx : dist b x = r)
    (hcxca : dist c x = dist c a) :
    p = x ∨ c = b := by
  have hpa_sq : dist p a ^ 2 = r ^ 2 := by rw [hpa]
  have hpb_sq : dist p b ^ 2 = r ^ 2 := by rw [hpb]
  have hpc_sq : dist p c ^ 2 = r ^ 2 := by rw [hpc]
  have hab_sq : dist a b ^ 2 = r ^ 2 := by rw [hab]
  have hax_sq : dist a x ^ 2 = r ^ 2 := by rw [hax]
  have hbx_sq : dist b x ^ 2 = r ^ 2 := by rw [hbx]
  have hcxca_sq : dist c x ^ 2 = dist c a ^ 2 := by rw [hcxca]
  rw [Erdos9796Mission.Internal.dist_sq_coords] at hpa_sq
  rw [Erdos9796Mission.Internal.dist_sq_coords] at hpb_sq
  rw [Erdos9796Mission.Internal.dist_sq_coords] at hpc_sq
  rw [Erdos9796Mission.Internal.dist_sq_coords] at hab_sq
  rw [Erdos9796Mission.Internal.dist_sq_coords] at hax_sq
  rw [Erdos9796Mission.Internal.dist_sq_coords] at hbx_sq
  rw [Erdos9796Mission.Internal.dist_sq_coords c x,
    Erdos9796Mission.Internal.dist_sq_coords c a] at hcxca_sq
  set a₀ := p 0 - a 0
  set a₁ := p 1 - a 1
  set b₀ := p 0 - b 0
  set b₁ := p 1 - b 1
  set c₀ := p 0 - c 0
  set c₁ := p 1 - c 1
  set x₀ := p 0 - x 0
  set x₁ := p 1 - x 1
  set R := r ^ 2
  set S := x₀ ^ 2 + x₁ ^ 2
  have hR : 0 < R := by positivity
  have haa : a₀ ^ 2 + a₁ ^ 2 = R := by
    simpa [a₀, a₁, R] using hpa_sq
  have hbb : b₀ ^ 2 + b₁ ^ 2 = R := by
    simpa [b₀, b₁, R] using hpb_sq
  have hcc : c₀ ^ 2 + c₁ ^ 2 = R := by
    simpa [c₀, c₁, R] using hpc_sq
  have hS : x₀ ^ 2 + x₁ ^ 2 = S := by simp [S]
  have habdot : a₀ * b₀ + a₁ * b₁ = R / 2 := by
    dsimp [a₀, a₁, b₀, b₁, R]
    nlinarith only [hpa_sq, hpb_sq, hab_sq]
  have haxdot : a₀ * x₀ + a₁ * x₁ = S / 2 := by
    dsimp [a₀, a₁, x₀, x₁, S, R]
    nlinarith only [hpa_sq, hax_sq]
  have hbxdot : b₀ * x₀ + b₁ * x₁ = S / 2 := by
    dsimp [b₀, b₁, x₀, x₁, S, R]
    nlinarith only [hpb_sq, hbx_sq]
  have hcxcaDot :
      c₀ * x₀ + c₁ * x₁ - (c₀ * a₀ + c₁ * a₁) =
        (S - R) / 2 := by
    dsimp [a₀, a₁, c₀, c₁, x₀, x₁, S, R]
    nlinarith only [hpa_sq, hpc_sq, hcxca_sq]
  rcases Erdos9796Mission.Internal.coordinate_collision hR haa hbb hcc hS habdot
      haxdot hbxdot hcxcaDot with hx | hcb
  · left
    have hx0 : p 0 = x 0 := by
      dsimp [x₀] at hx
      linarith [hx.1]
    have hx1 : p 1 = x 1 := by
      dsimp [x₁] at hx
      linarith [hx.2]
    ext i
    fin_cases i
    · exact hx0
    · exact hx1
  · right
    have hcb0 : c 0 = b 0 := by
      dsimp [c₀, b₀] at hcb
      linarith [hcb.1]
    have hcb1 : c 1 = b 1 := by
      dsimp [c₁, b₁] at hcb
      linarith [hcb.2]
    ext i
    fin_cases i
    · exact hcb0
    · exact hcb1
