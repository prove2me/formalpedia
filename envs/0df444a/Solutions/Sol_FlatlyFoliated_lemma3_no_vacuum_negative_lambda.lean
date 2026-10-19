-- Prove2me | solution 1 for FlatlyFoliated.lemma3_no_vacuum_negative_lambda
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:25:49.694891+00:00
-- url     : https://prove2.me/submissions/e682d05e-f6cc-4c5e-9cef-75dc84e5c4d6

import Theorems.Thm_FlatlyFoliated_radial_vacuum_identities

open scoped ContDiff Topology
open Set Filter FlatlyFoliated

namespace NegativeVacuum

private lemma radial_impossible (Λ R : ℝ) (hΛ : Λ < 0) (hR : 0 < R)
    (a e : ℝ → ℝ) (ha : Differentiable ℝ a) (he : Differentiable ℝ e)
    (hpos : ∀ r, 0 < e r)
    (hode : ∀ r, R < r → HasDerivAt (fun s => s * a s ^ 2) (Λ * r ^ 2 * e r ^ 2) r)
    (hmom : ∀ r, R < r → a r * deriv e r = 0) : False := by
  have hane : ∀ r, R < r → a r ≠ 0 := by
    intro r hr hz
    have hd := (hasDerivAt_id r).mul ((ha r).hasDerivAt.pow 2)
    have heq := hd.unique (hode r hr)
    have hp : 0 < r ^ 2 * e r ^ 2 := mul_pos (sq_pos_of_pos (hR.trans hr))
      (sq_pos_of_pos (hpos r))
    have hn : Λ * (r ^ 2 * e r ^ 2) < 0 := mul_neg_of_neg_of_pos hΛ hp
    change 1 * a r ^ 2 + r * ((2 : ℝ) * a r ^ (2 - 1) * deriv a r) = _ at heq
    have heq0 : (0 : ℝ) = Λ * r ^ 2 * e r ^ 2 := by
      calc
        0 = 1 * a r ^ 2 + r * ((2 : ℝ) * a r ^ (2 - 1) * deriv a r) := by simp [hz]
        _ = _ := heq
    nlinarith only [heq0, hn]
  have hed : ∀ r ∈ Ioi R, deriv e r = 0 := by
    intro r hr
    exact (mul_eq_zero.mp (hmom r hr)).resolve_left (hane r hr)
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
    (convex_Ioi R).isPreconnected he.differentiableOn (fun r hr => hed r hr)
  have hcpos : 0 < c := by rw [← hc (R + 1) (by simp)]; exact hpos _
  let q : ℝ := Λ * c ^ 2 / 3
  have hq : q < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hΛ
    (sq_pos_of_pos hcpos)) (by norm_num)
  let F : ℝ → ℝ := fun r => r * a r ^ 2
  let H : ℝ → ℝ := fun r => F r - q * r ^ 3
  have hHd : ∀ r ∈ Ioi R, HasDerivAt H 0 r := by
    intro r hr
    have hd := (hode r hr).sub (((hasDerivAt_id r).pow 3).const_mul q)
    have hz : Λ * r ^ 2 * e r ^ 2 - q * ((3 : ℝ) * r ^ (3 - 1) * 1) = 0 := by
      rw [hc r hr]
      dsimp [q]
      ring
    change HasDerivAt H (Λ * r ^ 2 * e r ^ 2 - q * ((3 : ℝ) * r ^ (3 - 1) * 1)) r at hd
    rw [hz] at hd
    exact hd
  obtain ⟨k, hk⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
    (convex_Ioi R).isPreconnected
    (fun r hr => (hHd r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hHd r hr).deriv)
  have ht : Tendsto (fun r : ℝ => q * r ^ 3 + k) atTop atBot :=
    tendsto_atBot_add_const_right _ k
      ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).const_mul_atTop_of_neg hq)
  have hev : ∀ᶠ r : ℝ in atTop, R < r ∧ q * r ^ 3 + k < 0 :=
    (eventually_gt_atTop R).and (ht.eventually (eventually_lt_atBot 0))
  obtain ⟨r, hr, hneg⟩ := hev.exists
  have hn : 0 ≤ F r := mul_nonneg (hR.trans hr).le (sq_nonneg _)
  have hrel := hk r hr
  dsimp [H] at hrel
  linarith

end NegativeVacuum

theorem solution (Λ : ℝ) (hΛ : Λ < 0) :
    ¬ ∃ (w : R3 → R3) (η : R3 → ℝ), ContDiff ℝ ∞ w ∧ ContDiff ℝ ∞ η ∧ (∀ x, 0 < η x) ∧
      FFREquations Λ 0 0 w η ∧ SphSymmAtInfty w η := by
  rintro ⟨w, η, hw, hη, hηpos, heq, hsph⟩
  obtain ⟨R, hR, hrad⟩ := radial_vacuum_identities Λ w η hw hη hηpos heq hsph
  let axis : ℝ → R3 := fun r => EuclideanSpace.single 0 r
  have haxis : ContDiff ℝ ∞ axis := by
    have heq : axis = fun r : ℝ => r • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
      funext r
      ext i
      by_cases hi : (0 : Fin 3) = i <;> simp [axis, hi]
    rw [heq]
    exact contDiff_id.smul contDiff_const
  apply NegativeVacuum.radial_impossible Λ R hΛ hR
    (fun r => w (axis r) 0) (fun r => η (axis r))
  · exact ((EuclideanSpace.proj 0 : R3 →L[ℝ] ℝ).contDiff.comp (hw.comp haxis)).differentiable
      (by simp)
  · exact (hη.comp haxis).differentiable (by simp)
  · exact fun r => hηpos _
  · exact fun r hr => (hrad r hr).1
  · exact fun r hr => (hrad r hr).2
