-- Prove2me | solution 1 for CelestialHolography.lorentzOfSL2C_orthochronous
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T14:35:28.25717+00:00
-- url     : https://prove2.me/submissions/955438be-79d3-476f-bbb3-bf0b24260295

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

set_option autoImplicit false

namespace CelestialHolography64cc

theorem quadPos (p q u v a1 a2 b1 b2 : ℝ) (hp : 0 < p) (hD : u ^ 2 + v ^ 2 < p * q)
    (hab : 0 < a1 ^ 2 + a2 ^ 2 + b1 ^ 2 + b2 ^ 2) :
    0 < p * (a1 ^ 2 + a2 ^ 2) + q * (b1 ^ 2 + b2 ^ 2) + 2 * u * (a1 * b1 + a2 * b2)
      - 2 * v * (a2 * b1 - a1 * b2) := by
  have hid : p * (p * (a1 ^ 2 + a2 ^ 2) + q * (b1 ^ 2 + b2 ^ 2) + 2 * u * (a1 * b1 + a2 * b2)
      - 2 * v * (a2 * b1 - a1 * b2)) = (p * a1 + u * b1 + v * b2) ^ 2
        + (p * a2 + u * b2 - v * b1) ^ 2 + (p * q - u ^ 2 - v ^ 2) * (b1 ^ 2 + b2 ^ 2) := by
    ring
  by_cases hb : b1 ^ 2 + b2 ^ 2 = 0
  · have h1 : b1 = 0 := by nlinarith [sq_nonneg b1, sq_nonneg b2]
    have h2 : b2 = 0 := by nlinarith [sq_nonneg b1, sq_nonneg b2]
    subst h1 h2
    have : 0 < a1 ^ 2 + a2 ^ 2 := by nlinarith
    nlinarith
  · have hb' : 0 < b1 ^ 2 + b2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hb)
    have hpos : 0 < (p * q - u ^ 2 - v ^ 2) * (b1 ^ 2 + b2 ^ 2) :=
      mul_pos (by linarith) hb'
    have : 0 < p * (p * (a1 ^ 2 + a2 ^ 2) + q * (b1 ^ 2 + b2 ^ 2) + 2 * u * (a1 * b1 + a2 * b2)
      - 2 * v * (a2 * b1 - a1 * b2)) := by
      rw [hid]; nlinarith [sq_nonneg (p * a1 + u * b1 + v * b2), sq_nonneg (p * a2 + u * b2 - v * b1)]
    exact pos_of_mul_pos_right this hp.le

theorem rowNZ (a b : ℂ) (h : a ≠ 0 ∨ b ≠ 0) : 0 < a.re ^ 2 + a.im ^ 2 + b.re ^ 2 + b.im ^ 2 := by
  rcases h with h | h
  · have : 0 < a.re ^ 2 + a.im ^ 2 := by
      have := Complex.normSq_pos.mpr h
      rw [Complex.normSq_apply] at this; nlinarith
    nlinarith [sq_nonneg b.re, sq_nonneg b.im]
  · have : 0 < b.re ^ 2 + b.im ^ 2 := by
      have := Complex.normSq_pos.mpr h
      rw [Complex.normSq_apply] at this; nlinarith
    nlinarith [sq_nonneg a.re, sq_nonneg a.im]

end CelestialHolography64cc

open CelestialHolography in
theorem solution (M : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (x : Fin 4 → ℝ) (hx0 : 0 < x 0) (hx : minkowskiNormSq x < 0) :
    0 < lorentzOfSL2C M x 0 := by
  have hdet : (M : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := M.2
  rw [Matrix.det_fin_two] at hdet
  simp [CelestialHolography.lorentzOfSL2C, CelestialHolography.fromHermitian,
    CelestialHolography.toHermitian, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply]
  unfold CelestialHolography.minkowskiNormSq at hx
  have hp : 0 < x 0 - x 3 := by nlinarith [sq_nonneg (x 1), sq_nonneg (x 2)]
  have hD : x 1 ^ 2 + x 2 ^ 2 < (x 0 - x 3) * (x 0 + x 3) := by nlinarith
  have r0 : (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ≠ 0 ∨ (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    rw [h.1, h.2] at hdet
    simp at hdet
  have r1 : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 ∨ (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    rw [h.1, h.2] at hdet
    simp at hdet
  have h0 := CelestialHolography64cc.quadPos _ _ _ _ _ _ _ _ hp hD (CelestialHolography64cc.rowNZ _ _ r0)
  have h1 := CelestialHolography64cc.quadPos _ _ _ _ _ _ _ _ hp hD (CelestialHolography64cc.rowNZ _ _ r1)
  linarith
