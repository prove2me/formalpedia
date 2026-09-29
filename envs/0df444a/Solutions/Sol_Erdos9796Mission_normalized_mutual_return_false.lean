-- Prove2me | solution 1 for Erdos9796Mission.normalized_mutual_return_false
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-12T21:38:54.266949+00:00
-- url     : https://prove2.me/submissions/f75d3753-31d6-42ca-a67c-831c97c3628c

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796Mission_NormalizedMutualReturn

/-!
# The normalized mutual-return obstruction

This is a standalone rehost of the affine-geometric proof from
`Erdos9796Proof/P97/ATail/ExactFiveMutualReturnChord.lean`.
-/

open scoped EuclideanGeometry

namespace Erdos9796Mission

private theorem affine_map_three {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : Plane →ᵃ[ℝ] E) (x y z : Plane) {a b c : ℝ}
    (hs : a + b + c = 1) :
    f (a • x + b • y + c • z) = a • f x + b • f y + c • f z := by
  have hd (p : Plane) : f p = f.linear p + f 0 := by
    simpa using f.map_vadd (0 : Plane) p
  rw [hd (a • x + b • y + c • z), hd x, hd y, hd z]
  simp only [map_add, map_smul, smul_add]
  have hh : (a + b + c) • f 0 = f 0 := by rw [hs, one_smul]
  conv_lhs => rw [← hh]
  module

private theorem convex_three {T : Set Plane} (hT : Convex ℝ T)
    {x y z : Plane} (hx : x ∈ T) (hy : y ∈ T) (hz : z ∈ T)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c = 1) : a • x + b • y + c • z ∈ T := by
  have hh := hT.sum_mem (t := Finset.univ) (w := ![a, b, c]) (z := ![x, y, z])
    (by intro i hi; fin_cases i <;> simp [*])
    (by simpa [Fin.sum_univ_succ, add_assoc] using hs)
    (by intro i hi; fin_cases i <;> simp [*])
  simpa [Fin.sum_univ_succ, add_assoc] using hh

private theorem not_convex_three {A : Finset Plane} (hA : ConvexIndep A)
    {p x y z : Plane} (hp : p ∈ A) (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxp : x ≠ p) (hyp : y ≠ p) (hzp : z ≠ p)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c = 1) (he : p = a • x + b • y + c • z) : False := by
  apply hA p hp
  rw [he] at hxp hyp hzp
  rw [he]
  apply convex_three (convex_convexHull ℝ _) _ _ _ ha hb hc hs
  all_goals apply subset_convexHull ℝ _
  · exact ⟨hx, hxp⟩
  · exact ⟨hy, hyp⟩
  · exact ⟨hz, hzp⟩

/- The upper equilateral placement is incompatible with the cap separator. -/
private theorem upper_placement_false
    {A : Finset Plane} (hconv : ConvexIndep A) {q O c b : Plane}
    (hqA : q ∈ A) (hOA : O ∈ A) (hcA : c ∈ A) (hbA : b ∈ A)
    (hbq : b ≠ q) (hcq : c ≠ q) (hOq : O ≠ q)
    (F : Plane →ᵃ[ℝ] Plane) (hF : Function.Injective F)
    {h k s σ : ℝ} (hh : 0 < h) (hk : 0 < k) (hs : 0 < s)
    (hFq : F q = planePoint (-1) 0) (hFO : F O = planePoint 0 (-σ * h))
    (hFc : F c = planePoint 0 (σ * k))
    (hFb : F b = planePoint (-(1 + s * k) / 2) (σ * ((k + s) / 2)))
    (L : Plane →ᵃ[ℝ] ℝ)
    (hLq : 0 < L q) (hLc : 0 < L c) (hLO : L O < 0) (hLb : L b < 0) : False := by
  let α := (1 + s * k) / 2
  let γ := s * (1 + k ^ 2) / (2 * (h + k))
  let β := 1 - α + γ
  have hα : 0 < α := by dsimp [α]; positivity
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hhk : h + k ≠ 0 := ne_of_gt (add_pos hh hk)
  have hsum : α + β + -γ = 1 := by dsimp [β]; ring
  have hbAffine : b = α • q + β • c + (-γ) • O := by
    apply hF
    rw [affine_map_three F q c O hsum, hFb, hFq, hFc, hFO]
    ext i
    fin_cases i <;>
      simp [planePoint, PiLp.add_apply, PiLp.smul_apply,
        α, β, γ] <;>
      field_simp <;> ring
  by_cases hβ : β ≤ 0
  · have hαne := ne_of_gt hα
    have hqAffine : q = α⁻¹ • b + (-β / α) • c + (γ / α) • O := by
      have he : α • q = b + (-β) • c + γ • O := by
        rw [hbAffine]
        module
      calc
        q = α⁻¹ • (α • q) := by
          rw [smul_smul, inv_mul_cancel₀ hαne, one_smul]
        _ = α⁻¹ • b + (-β / α) • c + (γ / α) • O := by
          rw [he]
          simp only [smul_add, smul_smul, div_eq_mul_inv]
          module
    have hconvsum : α⁻¹ + -β / α + γ / α = 1 := by
      field_simp
      dsimp [β]
      ring
    exact not_convex_three hconv hqA hbA hcA hOA hbq hcq hOq
      (inv_nonneg.mpr hα.le) (div_nonneg (neg_nonneg.mpr hβ) hα.le)
      (div_nonneg hγ.le hα.le) hconvsum hqAffine
  · have hβpos : 0 < β := lt_of_not_ge hβ
    have hL := congrArg L hbAffine
    rw [affine_map_three L q c O hsum] at hL
    simp only [smul_eq_mul] at hL
    nlinarith [mul_pos hα hLq, mul_pos hβpos hLc, mul_neg_of_pos_of_neg hγ hLO]

/- The lower equilateral placement is strictly inside the triangle with
   vertices `O,q,w` under the stated height bound. -/
private theorem lower_placement_false
    {A : Finset Plane} (hconv : ConvexIndep A) {q w O b : Plane}
    (hqA : q ∈ A) (hwA : w ∈ A) (hOA : O ∈ A) (hbA : b ∈ A)
    (hbO : b ≠ O) (hbq : b ≠ q) (hbw : b ≠ w)
    (F : Plane →ᵃ[ℝ] Plane) (hF : Function.Injective F)
    {h k s σ : ℝ} (hsq : s ^ 2 = 3) (hs : 0 < s) (hsh : s ≤ h)
    (hk : 0 < k) (hk1 : k ≤ 1)
    (hFq : F q = planePoint (-1) 0) (hFw : F w = planePoint 1 0)
    (hFO : F O = planePoint 0 (-σ * h))
    (hFb : F b = planePoint ((s * k - 1) / 2) (σ * ((k - s) / 2))) : False := by
  let x := (s * k - 1) / 2
  let δ := (s - k) / (2 * h)
  have hs1 : 1 < s := by nlinarith
  have hs2 : s < 2 := by nlinarith
  have hh : 0 < h := lt_of_lt_of_le hs hsh
  have hhne := ne_of_gt hh
  have hδ : 0 < δ :=
    div_pos (sub_pos.mpr (lt_of_le_of_lt hk1 hs1)) (mul_pos (by norm_num) hh)
  have hδhalf : δ < 1 / 2 := by
    dsimp [δ]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * h)).mpr
    linarith
  have hxlo : -(1 / 2) < x := by dsimp [x]; nlinarith [mul_pos hs hk]
  have hxhi : x < 1 / 2 := by dsimp [x]; nlinarith
  have hleft : 0 ≤ (1 - δ - x) / 2 := by linarith
  have hright : 0 ≤ (1 - δ + x) / 2 := by linarith
  have hsum : δ + (1 - δ - x) / 2 + (1 - δ + x) / 2 = 1 := by ring
  have hbAffine : b = δ • O + ((1 - δ - x) / 2) • q + ((1 - δ + x) / 2) • w := by
    apply hF
    rw [affine_map_three F O q w hsum, hFb, hFO, hFq, hFw]
    ext i
    fin_cases i <;>
      simp [planePoint, PiLp.add_apply, PiLp.smul_apply,
        x, δ] <;>
      field_simp <;> ring
  exact not_convex_three hconv hbA hOA hqA hwA hbO.symm hbq.symm hbw.symm
    hδ.le hleft hright hsum hbAffine

/- The two equal-radius equations determine the two equilateral placements. -/
private theorem equilateral_placements
    {k x y s : ℝ} (hsq : s ^ 2 = 3)
    (heq1 : (x + 1) ^ 2 + y ^ 2 = 1 + k ^ 2)
    (heq2 : x ^ 2 + (y - k) ^ 2 = 1 + k ^ 2) :
    (x = -(1 + s * k) / 2 ∧ y = (k + s) / 2) ∨
      (x = (s * k - 1) / 2 ∧ y = (k - s) / 2) := by
  have hlinear : 2 * x + 2 * k * y = k ^ 2 - 1 := by
    nlinarith [heq1, heq2]
  have hprod : (1 + k ^ 2) * ((2 * y - k) ^ 2 - s ^ 2) = 0 := by
    linear_combination
      (4 - (2 * x - 2 * k * y + 3 + k ^ 2)) * heq1 +
      (2 * x - 2 * k * y + 3 + k ^ 2) * heq2 - (1 + k ^ 2) * hsq
  have hsq' : (2 * y - k) ^ 2 - s ^ 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (by positivity)
  have hfactor : (2 * y - k - s) * (2 * y - k + s) = 0 := by nlinarith [hsq']
  rcases mul_eq_zero.mp hfactor with hupper | hlower
  · have hy : y = (k + s) / 2 := by linarith
    rw [hy] at hlinear
    exact Or.inl ⟨by nlinarith [hlinear], hy⟩
  · have hy : y = (k - s) / 2 := by linarith
    rw [hy] at hlinear
    exact Or.inr ⟨by nlinarith [hlinear], hy⟩

end Erdos9796Mission

open Erdos9796Mission

theorem solution
    {A : Finset Plane} (hconv : ConvexIndep A) {q w O c b : Plane}
    (hqA : q ∈ A) (hwA : w ∈ A) (hOA : O ∈ A) (hcA : c ∈ A) (hbA : b ∈ A)
    (hbO : b ≠ O) (hbq : b ≠ q) (hbw : b ≠ w) (hcq : c ≠ q) (hOq : O ≠ q)
    (F : Plane →ᵃ[ℝ] Plane) (hF : Function.Injective F)
    {h k x y s σ : ℝ} (_hσ : σ = 1 ∨ σ = -1)
    (hsq : s ^ 2 = 3) (hs : 0 < s) (hsh : s ≤ h) (hk : 0 < k) (hk1 : k ≤ 1)
    (hFq : F q = planePoint (-1) 0) (hFw : F w = planePoint 1 0)
    (hFO : F O = planePoint 0 (-σ * h)) (hFc : F c = planePoint 0 (σ * k))
    (hFb : F b = planePoint x (σ * y))
    (heq1 : (x + 1) ^ 2 + y ^ 2 = 1 + k ^ 2)
    (heq2 : x ^ 2 + (y - k) ^ 2 = 1 + k ^ 2)
    (L : Plane →ᵃ[ℝ] ℝ)
    (hLq : 0 < L q) (hLc : 0 < L c) (hLO : L O < 0) (hLb : L b < 0) : False := by
  rcases Erdos9796Mission.equilateral_placements hsq heq1 heq2 with
    ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [hx, hy] at hFb
    exact Erdos9796Mission.upper_placement_false hconv hqA hOA hcA hbA hbq hcq hOq F hF
      (lt_of_lt_of_le hs hsh) hk hs hFq hFO hFc hFb L hLq hLc hLO hLb
  · rw [hx, hy] at hFb
    exact Erdos9796Mission.lower_placement_false hconv hqA hwA hOA hbA hbO hbq hbw F hF
      hsq hs hsh hk hk1 hFq hFw hFO hFb
