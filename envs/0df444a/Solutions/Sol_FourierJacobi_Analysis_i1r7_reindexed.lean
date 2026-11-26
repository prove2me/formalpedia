-- Prove2me | solution 1 for FourierJacobi.Analysis.i1r7_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:03:23.486945+00:00
-- url     : https://prove2.me/submissions/7703db78-c374-4d0b-881c-588bd38069c2

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i1r7_cartan
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
    i1Raw t d U V T (i1r7Equiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (T * V * t / d) ^ n.1 * (t ^ 2) ^ n.2.1 * (T * U * t ^ 4) ^ n.2.2 := by
  rcases n with ⟨a, b, c⟩
  unfold i1Raw
  
  rw [i1r7_cartan]
  
  simp only [i1r7Equiv_val]
  have he : 3 * (-(a : ℤ)) + 2 * ((b : ℤ)) + 2 * (-(c : ℤ)-1) +
      3 * (-2*(-(c : ℤ)-1)) + 4 * (-(-(a : ℤ))) - 2 = ((a+2*b+4*c+2 : ℕ) : ℤ) := by omega
  have hk : -(a : ℤ) = -((a : ℕ) : ℤ) := by omega
  have hb : -(-(a : ℤ)) = ((a : ℕ) : ℤ) := by omega
  have hl : (-2*(-(c : ℤ)-1)) / 2 = ((c+1 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring
end FourierJacobi.Analysis
