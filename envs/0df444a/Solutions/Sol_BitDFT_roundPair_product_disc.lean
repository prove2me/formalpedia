-- Prove2me | solution 1 for BitDFT.roundPair_product_disc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T01:36:43.748988+00:00
-- url     : https://prove2.me/submissions/5b1b8c83-b925-4198-9847-cc5c7fa1b3cd

import Definitions.Def_BitDFT_Numerics
import Theorems.Thm_BitDFT_rounding_bridge
import Theorems.Thm_IntMul_HvdH_rho_bounds
set_option autoImplicit false
noncomputable section
open BitDFT

theorem solution (p : ℕ) (U V : ℤ × ℤ) (hU : inDisc p U) (hV : inDisc p V) :
    inDisc p (roundPair p (value p U * value p V)) := by
  change ‖value p U‖ ≤ 1 at hU
  change ‖value p V‖ ≤ 1 at hV
  unfold inDisc
  rw [BitDFT.rounding_bridge]
  have hcontract := (IntMul.HvdH.rho_bounds p (value p U * value p V)).1
  have hprod : ‖value p U * value p V‖ ≤ 1 := by
    rw [norm_mul]
    calc
      ‖value p U‖ * ‖value p V‖ ≤ 1 * ‖value p V‖ :=
        mul_le_mul_of_nonneg_right hU (norm_nonneg _)
      _ ≤ 1 := by simpa using hV
  exact hcontract.trans hprod
