-- Prove2me | solution 1 for FourierJacobi.Analysis.i1Raw_eq_shell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:22.130842+00:00
-- url     : https://prove2.me/submissions/a6aceefc-3dc0-4b87-8629-6bfc71147582

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace FourierJacobi.Analysis
theorem _root_.solution (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q * t ^ 2 = 1) (p : ℤ × ℤ × ℤ) (c : ℕ) :
    i1Raw t d U V T p c = shellCoeff q 1 * shellMonomial t d U V T 1 p c := by
  have hq : q = (t ^ 2)⁻¹ := by
    calc
      q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
      _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hqt, one_mul]
  have hi : q⁻¹ = t ^ 2 := by rw [hq, inv_inv]
  unfold i1Raw shellMonomial shellCoeff
  simp only [one_ne_zero, ↓reduceIte]
  rw [zpow_sub₀ ht, hi, hq]
  simp only [zpow_ofNat, div_eq_mul_inv]
  ring
end FourierJacobi.Analysis
