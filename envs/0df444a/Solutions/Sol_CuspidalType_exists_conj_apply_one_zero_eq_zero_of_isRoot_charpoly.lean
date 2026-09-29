-- Prove2me | solution 1 for CuspidalType.exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8a8ccedc-caaa-50a7-b0c4-c472990fc60e

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly

set_option autoImplicit false

open Polynomial CuspidalType

open Matrix

theorem solution
    (q : ℕ) [Fact q.Prime]
    (g : GL2 q) (x : ZMod q)
    (hx : (g : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x) :
    ∃ h : GL2 q, ((h * g * h⁻¹ : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := by
  set G : Matrix (Fin 2) (Fin 2) (ZMod q) := (g : Matrix (Fin 2) (Fin 2) (ZMod q)) with hG

  have hdet : ((Matrix.scalar (Fin 2)) x - G).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hx
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hGv : ∀ i, (G *ᵥ v) i = x * v i := by
    intro i
    have h := congrFun hv i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero, Matrix.scalar_apply,
      Matrix.mulVec_diagonal] at h
    exact h.symm
  have e0 : G 0 0 * v 0 + G 0 1 * v 1 = x * v 0 := by
    have := hGv 0; simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e1 : G 1 0 * v 0 + G 1 1 * v 1 = x * v 1 := by
    have := hGv 1; simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  by_cases ha : v 0 = 0
  ·
    have hb : v 1 ≠ 0 := by
      intro hb; apply hv0; ext i; fin_cases i <;> simp [ha, hb]
    let P : Matrix (Fin 2) (Fin 2) (ZMod q) := !![0, 1; v 1, 0]
    let Q : Matrix (Fin 2) (Fin 2) (ZMod q) := !![0, (v 1)⁻¹; 1, 0]
    have hQP : Q * P = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [P, Q, Matrix.mul_apply, Fin.sum_univ_two, hb]
    have hPQ : P * Q = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [P, Q, Matrix.mul_apply, Fin.sum_univ_two, hb]
    refine ⟨⟨Q, P, hQP, hPQ⟩, ?_⟩
    show (Q * G * P) 1 0 = 0
    have hval : (Q * G * P) 1 0 = G 0 1 * v 1 := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp [P, Q]
    rw [hval]
    rw [ha] at e0
    linear_combination e0
  ·
    let P : Matrix (Fin 2) (Fin 2) (ZMod q) := !![v 0, 0; v 1, 1]
    let Q : Matrix (Fin 2) (Fin 2) (ZMod q) := !![(v 0)⁻¹, 0; -(v 1 * (v 0)⁻¹), 1]
    have hQP : Q * P = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [P, Q, Matrix.mul_apply, Fin.sum_univ_two, ha]
    have hPQ : P * Q = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [P, Q, Matrix.mul_apply, Fin.sum_univ_two, ha]
    refine ⟨⟨Q, P, hQP, hPQ⟩, ?_⟩
    show (Q * G * P) 1 0 = 0
    have hinv : (v 0)⁻¹ * v 0 = 1 := inv_mul_cancel₀ ha
    have hval : (Q * G * P) 1 0 =
        (-(v 1 * (v 0)⁻¹) * G 0 0 + G 1 0) * v 0 + (-(v 1 * (v 0)⁻¹) * G 0 1 + G 1 1) * v 1 := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp [P, Q]
    rw [hval]
    linear_combination (-(v 1 * (v 0)⁻¹)) * e0 + e1 + (-(x * v 1)) * hinv

end S_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly
end P2MW
export P2MW.S_CuspidalType_exists_conj_apply_one_zero_eq_zero_of_isRoot_charpoly (solution)
