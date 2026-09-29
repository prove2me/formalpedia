-- Prove2me | solution 1 for FamousTheorems.machin_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:06:21.519791+00:00
-- url     : https://prove2.me/submissions/406c0412-728f-42f4-b503-0e6bd72a0859

import Mathlib

theorem solution : 4 * Real.arctan 5⁻¹ - Real.arctan 239⁻¹ = Real.pi / 4 :=
  Real.four_mul_arctan_inv_5_sub_arctan_inv_239
