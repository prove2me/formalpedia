-- Prove2me | solution 1 for FourierJacobi.Analysis.i1r4_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:21.906817+00:00
-- url     : https://prove2.me/submissions/b40f6a92-c420-42b4-813d-688688e58452

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i1r4_cartan
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
theorem _root_.solution (t d U V T : ℂ)  (depth : ℕ)
    (n : ℕ × ℕ × ℕ) :
    i1Raw t d U V T (i1r4Equiv n).val depth = ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (d * T * V * t) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 * (T * U * t ^ 2) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r4_cartan]
  
  simp only [i1r4Equiv_val]
  have he : 3 * ((a : ℤ)+1) + 2 * (-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4) + 2 * (-(a : ℤ)-(b : ℤ)-(c : ℤ)-3) +
      3 * (2*(-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4)-4*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)) + 4 * (2*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)-2*(-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4)-((a : ℤ)+1)) - 2 = ((a+2*b+2*c+3 : ℕ) : ℤ) := by omega
  have hk : (a : ℤ)+1 = ((a+1 : ℕ) : ℤ) := by omega
  have hb : 2*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)-2*(-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4)-((a : ℤ)+1) = ((a+2*b+1 : ℕ) : ℤ) := by omega
  have hl : (2*(-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4)-4*(-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)) / 2 = ((c+2 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring
end FourierJacobi.Analysis
