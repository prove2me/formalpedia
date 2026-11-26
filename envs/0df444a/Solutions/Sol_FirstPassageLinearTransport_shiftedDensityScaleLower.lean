-- Prove2me | solution 1 for FirstPassageLinearTransport.shiftedDensityScaleLower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:44:16.241097+00:00
-- url     : https://prove2.me/submissions/a4cadc3d-ee01-4d24-8161-507167306917

import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (gamma : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    (1 / 5 : ℝ) * ((M : ℝ) + 4) ^ (1 - gamma) ≤
      (M : ℝ) * ((M : ℝ) + 4) ^ (-gamma) := by
  have hx : (0 : ℝ) < (M : ℝ) + 4 := by positivity
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hfrac : ((M : ℝ) + 4) / 5 ≤ M := by
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hmul := mul_le_mul_of_nonneg_right hfrac
    (Real.rpow_nonneg hx.le (-gamma))
  calc
    (1 / 5 : ℝ) * ((M : ℝ) + 4) ^ (1 - gamma) =
        (((M : ℝ) + 4) / 5) * ((M : ℝ) + 4) ^ (-gamma) := by
      rw [show (1 : ℝ) - gamma = 1 + (-gamma) by ring,
        Real.rpow_add hx, Real.rpow_one]
      ring
    _ ≤ (M : ℝ) * ((M : ℝ) + 4) ^ (-gamma) := hmul
end FirstPassageLinearTransport
