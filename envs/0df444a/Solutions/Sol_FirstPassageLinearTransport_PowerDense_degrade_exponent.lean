-- Prove2me | solution 1 for FirstPassageLinearTransport.PowerDense.degrade_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:53.271596+00:00
-- url     : https://prove2.me/submissions/8df72a85-159a-4e29-ad18-ca629e2c0322

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_C_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_le_one
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_bad_bound

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace PowerDense
theorem _root_.solution {S : Set ℕ} {C D D' : ℝ}
    (h : PowerDense S C D) (hD' : 0 < D') (hD'D : D' ≤ D) :
    PowerDense S C D' := by
  refine ⟨h.C_pos, hD', hD'D.trans h.D_le_one, ?_⟩
  intro X hX
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hpow : (X : ℝ) ^ (1 - D) ≤ (X : ℝ) ^ (1 - D') :=
    Real.rpow_le_rpow_of_exponent_le hXR (by linarith)
  exact (h.bad_bound X hX).trans
    (mul_le_mul_of_nonneg_left hpow h.C_pos.le)
end PowerDense
end FirstPassageLinearTransport
