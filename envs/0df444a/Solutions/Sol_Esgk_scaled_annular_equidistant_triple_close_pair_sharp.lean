-- Prove2me | solution 1 for Esgk.scaled_annular_equidistant_triple_close_pair_sharp
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-20T05:09:04.245025+00:00
-- url     : https://prove2.me/submissions/6d8f6aec-a89e-4a17-94f8-35bf6bd14b21

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

lemma same_side_chord_sq_le {X Y X' Y' r : ℝ} (hr : 0 ≤ r)
    (h1 : X ^ 2 + Y ^ 2 = r ^ 2) (h2 : X' ^ 2 + Y' ^ 2 = r ^ 2) (hside : 0 ≤ Y * Y') :
    (X - X') ^ 2 + (Y - Y') ^ 2 ≤ 2 * r * |X - X'| := by
  have hX : |X| ≤ r := by
    apply abs_le_of_sq_le_sq' _ hr |>.elim (fun a b ↦ abs_le.mpr ⟨a, b⟩)
    nlinarith [sq_nonneg Y]
  have hX' : |X'| ≤ r := by
    apply abs_le_of_sq_le_sq' _ hr |>.elim (fun a b ↦ abs_le.mpr ⟨a, b⟩)
    nlinarith [sq_nonneg Y']
  obtain ⟨hXl, hXu⟩ := abs_le.mp hX
  obtain ⟨hXl', hXu'⟩ := abs_le.mp hX'
  set d := r * |X - X'| with hd
  have hd0 : 0 ≤ d := mul_nonneg hr (abs_nonneg _)
  have hdle : d ≤ r ^ 2 - X * X' := by
    rcases abs_cases (X - X') with ⟨h, -⟩ | ⟨h, -⟩
    · rw [hd, h]; nlinarith [mul_nonneg (sub_nonneg.mpr hXu) (neg_le_iff_add_nonneg.mp hXl')]
    · rw [hd, h]; nlinarith [mul_nonneg (sub_nonneg.mpr hXu') (neg_le_iff_add_nonneg.mp hXl)]
  have hid : (r ^ 2 - X * X') ^ 2 - (Y * Y') ^ 2 = d ^ 2 := by
    have : (Y * Y') ^ 2 = (r ^ 2 - X ^ 2) * (r ^ 2 - X' ^ 2) := by
      rw [mul_pow]; congr 1 <;> linarith
    rw [this, hd, mul_pow, sq_abs]; ring
  have hkey : r ^ 2 - X * X' - d ≤ Y * Y' := by
    by_cases hneg : r ^ 2 - X * X' - d ≤ 0
    · linarith
    · have hpos := not_le.mp hneg
      have hsq : (r ^ 2 - X * X' - d) ^ 2 ≤ (Y * Y') ^ 2 := by
        nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hdle)]
      nlinarith
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

theorem annular_equidistant_triple_close_pair_sharp (p : Point) (q : Fin 3 → Point)
    {x σ t : ℝ} (hσ : 0 < σ) (hσx : σ ^ 2 ≤ 1 - x) (ht : x * (σ + 1) ≤ σ * t)
    (hp : 1 - x ≤ ‖p‖ ^ 2)
    (hlo : ∀ i, 1 - x ≤ ‖q i‖ ^ 2) (hhi : ∀ i, ‖q i‖ ^ 2 ≤ 1)
    (heq : ∀ i j, dist p (q i) = dist p (q j)) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ t := by
  have hx : 0 ≤ x := by linarith [hlo 0, hhi 0]
  have ha : σ ≤ ‖p‖ := by nlinarith [norm_nonneg p]
  have ha0 : 0 < ‖p‖ := hσ.trans_le ha
  obtain ⟨u, v, hnorm, hdist, hapex⟩ := exists_apex_frame p q ha0.ne'
  obtain ⟨i, j, hij, hside⟩ := three_has_same_transverse_side v
  refine ⟨i, j, hij, ?_⟩
  have hqi : ‖q i‖ ≤ 1 := by nlinarith [norm_nonneg (q i), hhi i]
  have hrle : dist p (q i) ≤ ‖p‖ + 1 := by
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith)
  set a := ‖p‖
  set r := dist p (q i)
  have hr0 : 0 ≤ r := dist_nonneg
  have h1 : (u i - a) ^ 2 + v i ^ 2 = r ^ 2 := hapex i
  have h2 : (u j - a) ^ 2 + v j ^ 2 = r ^ 2 := by rw [hapex j, ← heq i j]
  have hchord := same_side_chord_sq_le hr0 h1 h2 hside
  rw [show u i - a - (u j - a) = u i - u j by ring, hdist] at hchord
  have hrow : 2 * a * (u i - u j) = ‖q i‖ ^ 2 - ‖q j‖ ^ 2 := by
    rw [← hnorm, ← hnorm]; linear_combination h2 - h1
  have hgap : 2 * a * |u i - u j| ≤ x := by
    have habs : |2 * a * (u i - u j)| ≤ x := by
      rw [hrow, abs_le]
      constructor <;> linarith [hlo i, hhi i, hlo j, hhi j]
    rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * a)] at habs
  have e1 : a * dist (q i) (q j) ^ 2 ≤ (a + 1) * x := by
    calc a * dist (q i) (q j) ^ 2 ≤ a * (2 * r * |u i - u j|) :=
          mul_le_mul_of_nonneg_left hchord ha0.le
      _ = r * (2 * a * |u i - u j|) := by ring
      _ ≤ r * x := mul_le_mul_of_nonneg_left hgap hr0
      _ ≤ (a + 1) * x := mul_le_mul_of_nonneg_right hrle hx
  have e2 : (a + 1) * x ≤ a * t := by
    have hσt : σ * ((a + 1) * x) ≤ σ * (a * t) := by
      nlinarith [mul_nonneg hx (sub_nonneg.mpr ha), mul_le_mul_of_nonneg_left ht ha0.le]
    exact le_of_mul_le_mul_left hσt hσ
  exact le_of_mul_le_mul_left (e1.trans e2) ha0

end

end Esgk

section

open EuclideanGeometry Esgk
open scoped RealInnerProductSpace

theorem solution
    (c p : Point) (q : Fin 3 → Point) {ρ x σ t : ℝ} (hρ : 0 < ρ)
    (hσ : 0 < σ) (hσx : σ ^ 2 ≤ 1 - x) (ht : x * (σ + 1) ≤ σ * t)
    (hp : ρ ^ 2 * (1 - x) ≤ dist p c ^ 2)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (q i) c ^ 2)
    (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2)
    (heq : ∀ i j, dist p (q i) = dist p (q j)) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ t * ρ ^ 2 := by
  let f : Point → Point := fun z ↦ ρ⁻¹ • (z - c)
  have hsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hf (z : Point) : ‖f z‖ ^ 2 = dist z c ^ 2 / ρ ^ 2 := by
    simp [f, norm_smul, Real.norm_eq_abs, dist_eq_norm, mul_pow, div_eq_mul_inv, mul_comm]
  have hd (z w : Point) : dist (f z) (f w) = dist z w / ρ := by
    simp only [f, dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, dist_sub_right]
    rw [div_eq_mul_inv, mul_comm]
  obtain ⟨i, j, hij, hclose⟩ := annular_equidistant_triple_close_pair_sharp (f p)
    (fun i ↦ f (q i)) hσ hσx ht
    (by rw [hf]; exact (le_div_iff₀ hsq).mpr (by nlinarith [hp]))
    (fun i ↦ by rw [hf]; exact (le_div_iff₀ hsq).mpr (by nlinarith [hlo i]))
    (fun i ↦ by rw [hf]; exact (div_le_iff₀ hsq).mpr (by simpa using hhi i))
    (fun i j ↦ by rw [hd, hd, heq i j])
  rw [hd, div_pow] at hclose
  exact ⟨i, j, hij, (div_le_iff₀ hsq).mp hclose⟩

end
