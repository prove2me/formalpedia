-- Prove2me | solution 1 for FourierJacobi.Analysis.i1r6a_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:20.693656+00:00
-- url     : https://prove2.me/submissions/78a3d711-154e-433f-8acf-de8c69010194

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i1r6a_cartan
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
    (n : ℕ × ℕ) :
    i1Raw t d U V T (i1r6aEquiv n).val depth = ((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (t ^ 2) ^ n.1 * (t ^ 2) ^ n.2 := by
  rcases n with ⟨a, b⟩
  unfold i1Raw
  
  rw [i1r6a_cartan]
  
  simp only [i1r6aEquiv_val]
  have he : 3 * (0) + 2 * ((a : ℤ)) + 2 * ((b : ℤ)) +
      3 * (0) + 4 * (1) - 2 = ((2*a+2*b+2 : ℕ) : ℤ) := by omega
  have hk : 0 = ((0 : ℕ) : ℤ) := by omega
  have hb : 1 = ((1 : ℕ) : ℤ) := by omega
  have hl : (0) / 2 = ((0 : ℕ) : ℤ) := by omega
  rw [he, hl, hb]
  try rw [hk]
  
  simp only [zpow_neg, zpow_natCast, zpow_ofNat, pow_add, pow_mul, mul_pow,
    pow_one, pow_zero, one_mul, mul_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring
end FourierJacobi.Analysis
