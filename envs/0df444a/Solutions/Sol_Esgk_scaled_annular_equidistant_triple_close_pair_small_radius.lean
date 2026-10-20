-- Prove2me | solution 1 for Esgk.scaled_annular_equidistant_triple_close_pair_small_radius
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-20T05:05:47.716998+00:00
-- url     : https://prove2.me/submissions/9214d824-5a00-4086-b61f-08d67405227e

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Esgk_PlanarGeneralPosition
import Definitions.Def_Esgk_Foundation

namespace Esgk

section


lemma three_has_same_transverse_side (v : Fin 3 → ℝ) :
    ∃ i j : Fin 3, i ≠ j ∧ 0 ≤ v i * v j := by
  by_cases h0 : 0 ≤ v 0 <;> by_cases h1 : 0 ≤ v 1 <;> by_cases h2 : 0 ≤ v 2
  · exact ⟨0, 1, by decide, mul_nonneg h0 h1⟩
  · exact ⟨0, 1, by decide, mul_nonneg h0 h1⟩
  · exact ⟨0, 2, by decide, mul_nonneg h0 h2⟩
  · exact ⟨1, 2, by decide, mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)⟩
  · exact ⟨1, 2, by decide, mul_nonneg h1 h2⟩
  · exact ⟨0, 2, by decide, mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)⟩
  · exact ⟨0, 1, by decide, mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)⟩
  · exact ⟨0, 1, by decide, mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)⟩

end

section

open EuclideanGeometry
open scoped BigOperators
variable {n : ℕ}

lemma point_dist_sq_coordinates (p q : Point) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

lemma point_norm_sq_coordinates (p : Point) :
    ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two]

end

section

open scoped RealInnerProductSpace

lemma same_side_chord_sq_le_of_sq_le {X Y X' Y' r γ : ℝ}
    (h1 : X ^ 2 + Y ^ 2 = r ^ 2) (h2 : X' ^ 2 + Y' ^ 2 = r ^ 2) (hside : 0 ≤ Y * Y')
    (hγ1 : γ ^ 2 ≤ 1) (hX : X ^ 2 ≤ γ ^ 2 * r ^ 2) (hX' : X' ^ 2 ≤ γ ^ 2 * r ^ 2) :
    (1 - γ ^ 2) * ((X - X') ^ 2 + (Y - Y') ^ 2) ≤ (X - X') ^ 2 := by
  have hg : 0 ≤ γ ^ 2 := sq_nonneg γ
  have hc : 0 ≤ 1 - γ ^ 2 := by linarith
  have hA : (1 - γ ^ 2) * X ^ 2 ≤ γ ^ 2 * Y ^ 2 := by nlinarith
  have hB : (1 - γ ^ 2) * X' ^ 2 ≤ γ ^ 2 * Y' ^ 2 := by nlinarith
  have hcross : (1 - γ ^ 2) * (X * X') ≤ γ ^ 2 * (Y * Y') := by
    have h0A : 0 ≤ (1 - γ ^ 2) * X ^ 2 := mul_nonneg hc (sq_nonneg _)
    have h0B : 0 ≤ (1 - γ ^ 2) * X' ^ 2 := mul_nonneg hc (sq_nonneg _)
    have hsq : ((1 - γ ^ 2) * (X * X')) ^ 2 ≤ (γ ^ 2 * (Y * Y')) ^ 2 := by
      calc ((1 - γ ^ 2) * (X * X')) ^ 2
          = ((1 - γ ^ 2) * X ^ 2) * ((1 - γ ^ 2) * X' ^ 2) := by ring
        _ ≤ (γ ^ 2 * Y ^ 2) * (γ ^ 2 * Y' ^ 2) := mul_le_mul hA hB h0B (h0A.trans hA)
        _ = (γ ^ 2 * (Y * Y')) ^ 2 := by ring
    exact (abs_le_of_sq_le_sq' hsq (mul_nonneg hg hside)).2
  have hsum : (1 - γ ^ 2) * (X + X') ^ 2 ≤ γ ^ 2 * (Y + Y') ^ 2 := by nlinarith
  have hdiff : (Y - Y') * (Y + Y') = -((X - X') * (X + X')) := by
    linear_combination h1 - h2
  have hid : (Y - Y') ^ 2 * (Y + Y') ^ 2 = (X - X') ^ 2 * (X + X') ^ 2 := by
    calc (Y - Y') ^ 2 * (Y + Y') ^ 2 = ((Y - Y') * (Y + Y')) ^ 2 := by ring
      _ = ((X - X') * (X + X')) ^ 2 := by rw [hdiff, neg_sq]
      _ = _ := by ring
  by_cases h0 : Y + Y' = 0
  · have hY' : Y' = -Y := by linarith
    rw [hY'] at hside
    have hY : Y = 0 := by nlinarith [sq_nonneg Y]
    have hYY : Y - Y' = 0 := by rw [hY', hY]; ring
    rw [hYY]
    nlinarith [sq_nonneg (X - X')]
  · have hpos : 0 < (Y + Y') ^ 2 := by positivity
    have key : (1 - γ ^ 2) * (Y - Y') ^ 2 ≤ γ ^ 2 * (X - X') ^ 2 := by
      have hm : (1 - γ ^ 2) * (Y - Y') ^ 2 * (Y + Y') ^ 2 ≤
          γ ^ 2 * (X - X') ^ 2 * (Y + Y') ^ 2 := by
        calc (1 - γ ^ 2) * (Y - Y') ^ 2 * (Y + Y') ^ 2
            = (X - X') ^ 2 * ((1 - γ ^ 2) * (X + X') ^ 2) := by
              rw [mul_assoc, hid]; ring
          _ ≤ (X - X') ^ 2 * (γ ^ 2 * (Y + Y') ^ 2) :=
              mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
          _ = γ ^ 2 * (X - X') ^ 2 * (Y + Y') ^ 2 := by ring
      exact le_of_mul_le_mul_right hm hpos
    nlinarith

private lemma exists_apex_frame (p : Point) (q : Fin 3 → Point) (ha0 : ‖p‖ ≠ 0) :
    ∃ u v : Fin 3 → ℝ, (∀ i, u i ^ 2 + v i ^ 2 = ‖q i‖ ^ 2) ∧
      (∀ i j, (u i - u j) ^ 2 + (v i - v j) ^ 2 = dist (q i) (q j) ^ 2) ∧
      ∀ i, (u i - ‖p‖) ^ 2 + v i ^ 2 = dist p (q i) ^ 2 := by
  set a := ‖p‖ with ha
  have hpa : p 0 ^ 2 + p 1 ^ 2 = a ^ 2 := (point_norm_sq_coordinates p).symm
  let u : Fin 3 → ℝ := fun i ↦ (p 0 * q i 0 + p 1 * q i 1) / a
  let v : Fin 3 → ℝ := fun i ↦ (-p 1 * q i 0 + p 0 * q i 1) / a
  have hnorm (i : Fin 3) : u i ^ 2 + v i ^ 2 = ‖q i‖ ^ 2 := by
    rw [point_norm_sq_coordinates]
    dsimp [u, v]
    field_simp [ha0]
    calc
      _ = (p 0 ^ 2 + p 1 ^ 2) * (q i 0 ^ 2 + q i 1 ^ 2) := by ring
      _ = _ := by rw [hpa]
  have hdist (i j : Fin 3) :
      (u i - u j) ^ 2 + (v i - v j) ^ 2 = dist (q i) (q j) ^ 2 := by
    rw [point_dist_sq_coordinates]
    dsimp [u, v]
    field_simp [ha0]
    calc
      _ = (p 0 ^ 2 + p 1 ^ 2) *
          ((q i 0 - q j 0) ^ 2 + (q i 1 - q j 1) ^ 2) := by ring
      _ = _ := by rw [hpa]
  have hapex (i : Fin 3) : (u i - a) ^ 2 + v i ^ 2 = dist p (q i) ^ 2 := by
    have hu : a * u i = p 0 * q i 0 + p 1 * q i 1 := by
      dsimp [u]; field_simp [ha0]
    calc
      _ = a ^ 2 - 2 * (a * u i) + (u i ^ 2 + v i ^ 2) := by ring
      _ = _ := by
        rw [hnorm, hu, point_norm_sq_coordinates, point_dist_sq_coordinates,
          point_norm_sq_coordinates]
        nlinarith [hpa]
  exact ⟨u, v, hnorm, hdist, hapex⟩

private lemma sq_add_le_two_mul_of_mem {r x κ γ : ℝ} (hx : 0 ≤ x) (hκ : 0 < κ)
    (hγ : 0 ≤ γ) (hC2 : κ ^ 2 * x + 1 ≤ 2 * γ * κ) (hC3 : (3 + x) ^ 2 ≤ 12 * γ ^ 2)
    (hbig : κ * x ≤ r) (hr3 : r ^ 2 ≤ 3) :
    r ^ 2 + x ≤ 2 * γ * r := by
  have hr0 : 0 ≤ r := (mul_nonneg hκ.le hx).trans hbig
  set m := κ ^ 2 * x ^ 2 with hm
  have hm0 : 0 ≤ m := by positivity
  have hmR : m ≤ r ^ 2 := by
    rw [hm, ← mul_pow]; exact pow_le_pow_left₀ (mul_nonneg hκ.le hx) hbig 2
  have hfm : (m + x) ^ 2 ≤ 4 * γ ^ 2 * m := by
    have hlin : m + x ≤ 2 * γ * κ * x := by
      rw [hm]; nlinarith [mul_le_mul_of_nonneg_right hC2 hx]
    have h0 : 0 ≤ m + x := by linarith
    calc (m + x) ^ 2 ≤ (2 * γ * κ * x) ^ 2 := pow_le_pow_left₀ h0 hlin 2
      _ = 4 * γ ^ 2 * m := by rw [hm]; ring
  have hf3 : (3 + x) ^ 2 ≤ 4 * γ ^ 2 * 3 := by linarith
  set R := r ^ 2 with hR
  have hlinR : (2 * x - 4 * γ ^ 2 + m + 3) * R + x ^ 2 - 3 * m ≤ 0 := by
    rcases le_total 0 (2 * x - 4 * γ ^ 2 + m + 3) with hs | hs
    · nlinarith [mul_le_mul_of_nonneg_left hr3 hs]
    · nlinarith [mul_le_mul_of_nonpos_left hmR hs]
  have hf : (R + x) ^ 2 ≤ (2 * γ * r) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmR) (sub_nonneg.mpr hr3)]
  exact (abs_le_of_sq_le_sq' hf (by positivity)).2

private lemma offset_sq_le {a r x σ κ γ X N : ℝ} (hσ : 0 < σ) (hσx : σ ^ 2 ≤ 1 - x)
    (hκ : 0 < κ) (hγ : 0 ≤ γ) (hCu : 1 ≤ 2 * σ * γ * κ) (hC1 : 3 ≤ 4 * γ ^ 2 * σ ^ 2)
    (hC2 : κ ^ 2 * x + 1 ≤ 2 * γ * κ) (hC3 : (3 + x) ^ 2 ≤ 12 * γ ^ 2)
    (hx : 0 ≤ x) (hσa : σ ≤ a) (ha1 : a ≤ 1) (ha2 : 1 - x ≤ a ^ 2)
    (hbig : κ * x ≤ r) (hr3 : r ^ 2 ≤ 3)
    (hN : N = r ^ 2 + 2 * a * X + a ^ 2) (hlo : 1 - x ≤ N) (hhi : N ≤ 1) :
    X ^ 2 ≤ γ ^ 2 * r ^ 2 := by
  have hr0 : 0 ≤ r := (mul_nonneg hκ.le hx).trans hbig
  have ha0 : 0 < a := hσ.trans_le hσa
  have hγr : 0 ≤ γ * r := mul_nonneg hγ hr0
  have hup : X ≤ γ * r := by
    have h1 : 2 * a * X ≤ x := by nlinarith [sq_nonneg r]
    have h2 : x ≤ 2 * σ * γ * (κ * x) := by nlinarith [mul_le_mul_of_nonneg_right hCu hx]
    have h3 : 2 * σ * γ * (κ * x) ≤ 2 * a * (γ * r) := by
      have : σ * (γ * (κ * x)) ≤ a * (γ * r) :=
        mul_le_mul hσa (mul_le_mul_of_nonneg_left hbig hγ)
          (mul_nonneg hγ (mul_nonneg hκ.le hx)) ha0.le
      linarith
    have h4 : a * X ≤ a * (γ * r) := by linarith
    exact le_of_mul_le_mul_left h4 ha0
  have hgσ : σ ^ 2 - 2 * γ * r * σ + r ^ 2 - (1 - x) ≤ 0 := by
    have hr2 : r ≤ 2 * γ * σ := by
      have hsq : r ^ 2 ≤ (2 * γ * σ) ^ 2 := by nlinarith
      exact (abs_le_of_sq_le_sq' hsq (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hr2 hr0]
  have hg1 : 1 - 2 * γ * r + r ^ 2 - (1 - x) ≤ 0 := by
    have := sq_add_le_two_mul_of_mem hx hκ hγ hC2 hC3 hbig hr3
    linarith
  have hga : a ^ 2 - 2 * γ * r * a + r ^ 2 - (1 - x) ≤ 0 := by
    have hq : (a - σ) * (a - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hσa) (sub_nonpos.mpr ha1)
    rcases le_total 0 (σ + 1 - 2 * γ * r) with hs | hs
    · nlinarith [mul_le_mul_of_nonneg_left ha1 hs]
    · nlinarith [mul_le_mul_of_nonpos_left hσa hs]
  have hlow : -(γ * r) ≤ X := by
    have h4 : a * (-(γ * r)) ≤ a * X := by nlinarith
    exact le_of_mul_le_mul_left h4 ha0
  calc X ^ 2 ≤ (γ * r) ^ 2 := sq_le_sq' hlow hup
    _ = γ ^ 2 * r ^ 2 := by ring

theorem annular_equidistant_triple_close_pair_small_radius (p : Point) (q : Fin 3 → Point)
    {x σ κ γ t : ℝ} (hσ : 0 < σ) (hσx : σ ^ 2 ≤ 1 - x) (hκ : 0 < κ) (hγ : 0 ≤ γ)
    (hγ1 : γ ^ 2 < 1) (hCu : 1 ≤ 2 * σ * γ * κ) (hC1 : 3 ≤ 4 * γ ^ 2 * σ ^ 2)
    (hC2 : κ ^ 2 * x + 1 ≤ 2 * γ * κ) (hC3 : (3 + x) ^ 2 ≤ 12 * γ ^ 2)
    (ht1 : 4 * κ ^ 2 * x ^ 2 ≤ t) (ht2 : x ^ 2 ≤ 4 * σ ^ 2 * (1 - γ ^ 2) * t)
    (hp : 1 - x ≤ ‖p‖ ^ 2) (hp1 : ‖p‖ ^ 2 ≤ 1)
    (hlo : ∀ i, 1 - x ≤ ‖q i‖ ^ 2) (hhi : ∀ i, ‖q i‖ ^ 2 ≤ 1)
    (heq : ∀ i j, dist p (q i) = dist p (q j)) (hr : ∀ i, dist p (q i) ^ 2 ≤ 3) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ t := by
  have hx : 0 ≤ x := by linarith [hlo 0, hhi 0]
  obtain ⟨r, hrk⟩ : ∃ r, ∀ k, dist p (q k) = r := ⟨dist p (q 0), fun k ↦ heq k 0⟩
  have hr0 : 0 ≤ r := hrk 0 ▸ dist_nonneg
  have hr3 : r ^ 2 ≤ 3 := hrk 0 ▸ hr 0
  by_cases hsmall : r < κ * x
  · refine ⟨0, 1, by decide, ?_⟩
    have htri : dist (q 0) (q 1) ≤ 2 * r := by
      calc dist (q 0) (q 1) ≤ dist (q 0) p + dist p (q 1) := dist_triangle _ _ _
        _ = 2 * r := by rw [dist_comm, hrk 0, hrk 1]; ring
    have h0 : 0 ≤ dist (q 0) (q 1) := dist_nonneg
    nlinarith [mul_le_mul htri htri h0 (by linarith), mul_self_lt_mul_self hr0 hsmall]
  have hbig : κ * x ≤ r := not_lt.mp hsmall
  have ha : σ ≤ ‖p‖ := by nlinarith [norm_nonneg p]
  have ha0 : 0 < ‖p‖ := hσ.trans_le ha
  have ha1 : ‖p‖ ≤ 1 := by nlinarith [norm_nonneg p]
  obtain ⟨u, v, hnorm, hdist, hapex⟩ := exists_apex_frame p q ha0.ne'
  set a := ‖p‖
  have hXk (k : Fin 3) : (u k - a) ^ 2 ≤ γ ^ 2 * r ^ 2 := by
    refine offset_sq_le hσ hσx hκ hγ hCu hC1 hC2 hC3 hx ha ha1 hp hbig hr3
      (N := ‖q k‖ ^ 2) ?_ (hlo k) (hhi k)
    have hk := hapex k
    rw [hrk k] at hk
    rw [← hnorm k]
    linear_combination hk
  obtain ⟨i, j, hij, hside⟩ := three_has_same_transverse_side v
  refine ⟨i, j, hij, ?_⟩
  have h1 : (u i - a) ^ 2 + v i ^ 2 = r ^ 2 := by rw [hapex i, hrk i]
  have h2 : (u j - a) ^ 2 + v j ^ 2 = r ^ 2 := by rw [hapex j, hrk j]
  have hchord := same_side_chord_sq_le_of_sq_le h1 h2 hside hγ1.le (hXk i) (hXk j)
  rw [show u i - a - (u j - a) = u i - u j by ring, hdist] at hchord
  have hrow : 2 * a * (u i - u j) = ‖q i‖ ^ 2 - ‖q j‖ ^ 2 := by
    rw [← hnorm, ← hnorm]; linear_combination h2 - h1
  have hgap : (2 * a * (u i - u j)) ^ 2 ≤ x ^ 2 := by
    rw [hrow]
    exact sq_le_sq' (by linarith [hlo i, hhi i, hlo j, hhi j])
      (by linarith [hlo i, hhi i, hlo j, hhi j])
  have hσa2 : σ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hσ.le ha 2
  have hc : 0 < 4 * σ ^ 2 * (1 - γ ^ 2) := by
    have : 0 < 1 - γ ^ 2 := by linarith
    positivity
  have hmain : 4 * σ ^ 2 * (1 - γ ^ 2) * dist (q i) (q j) ^ 2 ≤
      4 * σ ^ 2 * (1 - γ ^ 2) * t := by
    calc 4 * σ ^ 2 * (1 - γ ^ 2) * dist (q i) (q j) ^ 2
        = 4 * σ ^ 2 * ((1 - γ ^ 2) * dist (q i) (q j) ^ 2) := by ring
      _ ≤ 4 * σ ^ 2 * (u i - u j) ^ 2 :=
          mul_le_mul_of_nonneg_left hchord (by positivity)
      _ ≤ 4 * a ^ 2 * (u i - u j) ^ 2 := by
          gcongr
      _ = (2 * a * (u i - u j)) ^ 2 := by ring
      _ ≤ x ^ 2 := hgap
      _ ≤ 4 * σ ^ 2 * (1 - γ ^ 2) * t := ht2
  exact le_of_mul_le_mul_left hmain hc

end

end Esgk

section

open EuclideanGeometry Esgk
open scoped RealInnerProductSpace

theorem solution
    (c p : Point) (q : Fin 3 → Point) {ρ x σ κ γ t : ℝ} (hρ : 0 < ρ)
    (hσ : 0 < σ) (hσx : σ ^ 2 ≤ 1 - x) (hκ : 0 < κ) (hγ : 0 ≤ γ)
    (hγ1 : γ ^ 2 < 1) (hCu : 1 ≤ 2 * σ * γ * κ) (hC1 : 3 ≤ 4 * γ ^ 2 * σ ^ 2)
    (hC2 : κ ^ 2 * x + 1 ≤ 2 * γ * κ) (hC3 : (3 + x) ^ 2 ≤ 12 * γ ^ 2)
    (ht1 : 4 * κ ^ 2 * x ^ 2 ≤ t) (ht2 : x ^ 2 ≤ 4 * σ ^ 2 * (1 - γ ^ 2) * t)
    (hp : ρ ^ 2 * (1 - x) ≤ dist p c ^ 2) (hp1 : dist p c ^ 2 ≤ ρ ^ 2)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (q i) c ^ 2)
    (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2)
    (heq : ∀ i j, dist p (q i) = dist p (q j))
    (hr : ∀ i, dist p (q i) ^ 2 ≤ 3 * ρ ^ 2) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ t * ρ ^ 2 := by
  let f : Point → Point := fun z ↦ ρ⁻¹ • (z - c)
  have hsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hf (z : Point) : ‖f z‖ ^ 2 = dist z c ^ 2 / ρ ^ 2 := by
    simp [f, norm_smul, Real.norm_eq_abs, dist_eq_norm, mul_pow, div_eq_mul_inv, mul_comm]
  have hd (z w : Point) : dist (f z) (f w) = dist z w / ρ := by
    simp only [f, dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, dist_sub_right]
    rw [div_eq_mul_inv, mul_comm]
  obtain ⟨i, j, hij, hclose⟩ := annular_equidistant_triple_close_pair_small_radius (f p)
    (fun i ↦ f (q i)) hσ hσx hκ hγ hγ1 hCu hC1 hC2 hC3 ht1 ht2
    (by rw [hf]; exact (le_div_iff₀ hsq).mpr (by nlinarith [hp]))
    (by rw [hf]; exact (div_le_iff₀ hsq).mpr (by simpa using hp1))
    (fun i ↦ by rw [hf]; exact (le_div_iff₀ hsq).mpr (by nlinarith [hlo i]))
    (fun i ↦ by rw [hf]; exact (div_le_iff₀ hsq).mpr (by simpa using hhi i))
    (fun i j ↦ by rw [hd, hd, heq i j])
    (fun i ↦ by rw [hd, div_pow]; exact (div_le_iff₀ hsq).mpr (hr i))
  rw [hd, div_pow] at hclose
  exact ⟨i, j, hij, (div_le_iff₀ hsq).mp hclose⟩

end
