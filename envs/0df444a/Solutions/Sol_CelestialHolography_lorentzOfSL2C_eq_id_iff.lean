-- Prove2me | solution 1 for CelestialHolography.lorentzOfSL2C_eq_id_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:11:39.353987+00:00
-- url     : https://prove2.me/submissions/c5c0b844-be21-47d1-a74d-503129fb55ca

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

set_option autoImplicit false

namespace CelestialHolography

theorem lorentzOfSL2C_one_apply_aux (x : Fin 4 → ℝ) : lorentzOfSL2C 1 x = x := by
  funext i
  fin_cases i <;> simp [lorentzOfSL2C, fromHermitian, toHermitian]

theorem lorentzOfSL2C_neg_one_apply_aux (x : Fin 4 → ℝ) : lorentzOfSL2C (-1) x = x := by
  funext i
  fin_cases i <;> simp [lorentzOfSL2C, fromHermitian, toHermitian]

theorem lorentz_real_core_aux (a1 a2 b1 b2 c1 c2 d1 d2 : ℝ)
    (hA : a1 * a1 + a2 * a2 = 1) (hB : b1 * b1 + b2 * b2 = 0) (hC : c1 * c1 + c2 * c2 = 0)
    (hr : a1 * d1 - a2 * d2 - (b1 * c1 - b2 * c2) = 1)
    (hi : a1 * d2 + a2 * d1 - (b1 * c2 + b2 * c1) = 0)
    (j1 : b1 * c1 + b2 * c2 + (a1 * d1 + a2 * d2) = 1)
    (j2 : b2 * c1 - b1 * c2 + (a2 * d1 - a1 * d2) = 0) :
    b1 = 0 ∧ b2 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ a2 = 0 ∧ d2 = 0 ∧
      ((a1 = 1 ∧ d1 = 1) ∨ (a1 = -1 ∧ d1 = -1)) := by
  obtain ⟨hb1, hb2⟩ := mul_self_add_mul_self_eq_zero.mp hB
  obtain ⟨hc1, hc2⟩ := mul_self_add_mul_self_eq_zero.mp hC
  subst hb1 hb2 hc1 hc2
  have h11 : a1 * d1 = 1 := by linarith
  have h22 : a2 * d2 = 0 := by linarith
  have h12 : a1 * d2 = 0 := by linarith
  have h21 : a2 * d1 = 0 := by linarith
  have ha2 : a2 = 0 := by linear_combination (-a2) * h11 + a1 * h21
  have hd2 : d2 = 0 := by linear_combination (-d2) * h11 + d1 * h12
  subst ha2 hd2
  have ha : a1 * a1 = 1 := by linarith
  have hda : d1 = a1 := by linear_combination (-d1) * ha + a1 * h11
  subst hda
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rcases mul_self_eq_one_iff.mp ha with h | h
  · exact Or.inl ⟨h, h⟩
  · exact Or.inr ⟨h, h⟩

theorem lorentzOfSL2C_fix_forward_aux (M : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (h : ∀ x : Fin 4 → ℝ, lorentzOfSL2C M x = x) : M = 1 ∨ M = -1 := by
  have e0 := h ![1,0,0,0]
  have k0 := congrFun e0 0
  have k3 := congrFun e0 3
  simp [lorentzOfSL2C, fromHermitian, toHermitian, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im] at k0 k3
  have e3 := h ![0,0,0,1]
  have m0 := congrFun e3 0
  have m3 := congrFun e3 3
  simp [lorentzOfSL2C, fromHermitian, toHermitian, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im] at m0 m3
  have e1 := h ![0,1,0,0]
  have j1 := congrFun e1 1
  have j2 := congrFun e1 2
  simp [lorentzOfSL2C, fromHermitian, toHermitian, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.mul_re, Complex.mul_im] at j1 j2
  have hd := M.2
  rw [Matrix.det_fin_two] at hd
  have hr := congrArg Complex.re hd
  have hi := congrArg Complex.im hd
  simp [Complex.mul_re, Complex.mul_im] at hr hi
  clear h e0 e1 e3 hd
  obtain ⟨hb1, hb2, hc1, hc2, ha2, hd2, hfin⟩ := lorentz_real_core_aux
    ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im
    ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im
    ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im
    ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 1).re ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 1).im
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)
  rcases hfin with ⟨ha1, hd1⟩ | ⟨ha1, hd1⟩
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [ha1, hd1, ha2, hd2, hb1, hb2, hc1, hc2]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [ha1, hd1, ha2, hd2, hb1, hb2, hc1, hc2]

end CelestialHolography

open CelestialHolography in
theorem solution (M : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    (∀ x : Fin 4 → ℝ, lorentzOfSL2C M x = x) ↔ M = 1 ∨ M = -1 := by
  constructor
  · exact CelestialHolography.lorentzOfSL2C_fix_forward_aux M
  · rintro (rfl | rfl)
    · exact CelestialHolography.lorentzOfSL2C_one_apply_aux
    · exact CelestialHolography.lorentzOfSL2C_neg_one_apply_aux
