-- Prove2me | solution 2 for ENNReal.cancel_common_numerator_in_division_ratio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:28.066968+00:00
-- url     : https://prove2.me/submissions/88b0a9e7-3067-40f9-9981-25927886a8a4

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000


theorem solution {a b c : ENNReal} (ha : a ≠ 0) (ha' : a ≠ ⊤)
    (hc : c ≠ ⊤) :
    (a / b) / (a / c) = c / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl ha) (Or.inl ha'), inv_inv]
  rw [show a * b⁻¹ * (a⁻¹ * c) = (a * a⁻¹) * (c * b⁻¹) by ring, ENNReal.mul_inv_cancel ha ha', one_mul]
  exact (div_eq_mul_inv c b).symm

