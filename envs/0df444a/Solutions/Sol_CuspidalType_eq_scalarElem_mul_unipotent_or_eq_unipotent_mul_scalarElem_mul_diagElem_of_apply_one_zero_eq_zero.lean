-- Prove2me | solution 1 for CuspidalType.eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/48c446fc-4af6-5a64-aac9-ab2070cad34c

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero

set_option autoImplicit false

p2m_open "Polynomial CuspidalType P2MW.S_CuspidalType_eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero.CuspidalType"

namespace CuspidalType p2m_export "CuspidalType" "GL2 unipotent scalarElem diagElem" end CuspidalType
p2m_open_scoped "CuspidalType" in
theorem CuspidalType.coe_scalarElem' (q : ℕ) [Fact q.Prime] (c : (ZMod q)ˣ) :
    ((scalarElem q c : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) = Matrix.scalar (Fin 2) (c : ZMod q) := rfl

theorem solution
    (q : ℕ) [Fact q.Prime]
    (b : GL2 q) (hb : (b : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0) :
    (∃ (c : (ZMod q)ˣ) (t : ZMod q), b = scalarElem q c * unipotent q t) ∨
    (∃ (a d : (ZMod q)ˣ) (s : ZMod q), a ≠ d ∧ b = unipotent q s * (scalarElem q d * diagElem q (a * d⁻¹))) := by
  have hdetB : (b.val).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _ |>.mp b.isUnit).ne_zero
  have hdet2 : (b.val).det = b.val 0 0 * b.val 1 1 := by
    rw [Matrix.det_fin_two]; rw [show b.val 1 0 = 0 from hb, mul_zero, sub_zero]
  have hx : b.val 0 0 ≠ 0 := fun h => hdetB (by rw [hdet2, h, zero_mul])
  have hw : b.val 1 1 ≠ 0 := fun h => hdetB (by rw [hdet2, h, mul_zero])
  have hb' : b.val 1 0 = 0 := hb
  by_cases hxw : b.val 0 0 = b.val 1 1
  · left
    refine ⟨Units.mk0 (b.val 0 0) hx, b.val 0 1 * (b.val 0 0)⁻¹, ?_⟩
    apply Units.ext
    rw [Units.val_mul, CuspidalType.coe_scalarElem']
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hb']
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hxw]
  · right
    refine ⟨Units.mk0 (b.val 0 0) hx, Units.mk0 (b.val 1 1) hw, b.val 0 1 * (b.val 1 1)⁻¹, fun h => hxw ?_, ?_⟩
    · have := congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) h
      simpa using this
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, CuspidalType.coe_scalarElem']
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
    · simp [Matrix.mul_apply, Fin.sum_univ_two, hb']
    · simp [Matrix.mul_apply, Fin.sum_univ_two]

end S_CuspidalType_eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero
end P2MW
export P2MW.S_CuspidalType_eq_scalarElem_mul_unipotent_or_eq_unipotent_mul_scalarElem_mul_diagElem_of_apply_one_zero_eq_zero (solution)
