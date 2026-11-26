-- Prove2me | solution 1 for FirstPassageLinearTransport.normalized_card_shellMultiplicativeHit_quarter_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:14:29.7245+00:00
-- url     : https://prove2.me/submissions/317e5741-773a-4040-8d60-3e5ceb3f4ff9

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_normalized_card_shellMultiplicativeHit_le_inv

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {R : ℝ} (hR : 0 < R) (M : ℕ) :
    ((shellMultiplicativeHit M (R / 4)).card : ℝ) /
        (2 : ℝ) ^ M ≤ 4 / R := by
  have h := normalized_card_shellMultiplicativeHit_le_inv
    (u := R / 4) (by positivity) M
  calc
    _ ≤ (R / 4)⁻¹ := h
    _ = 4 / R := by field_simp
end FirstPassageLinearTransport
