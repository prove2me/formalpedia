-- Prove2me | solution 1 for FourierJacobi.Analysis.i0_middle_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:01.876666+00:00
-- url     : https://prove2.me/submissions/e8431c08-ec8f-42a4-8655-2abb43849905

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_i0MiddleRow_cartan
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
namespace FourierJacobi.Analysis
theorem _root_.solution (neg : Bool) (t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0MiddleRowEquiv neg n).val =
      ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * U * t ^ 2)) *
        (i0KRatio neg t d V T) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 *
        (T * U * t ^ 2) ^ n.2.2 := by
  unfold i0Shell
  rw [i0MiddleRow_cartan]
  cases neg <;> simp only [i0MiddleRowEquiv, Equiv.coe_fn_mk, i0KInitial,
    i0KRatio, Bool.false_eq_true, ↓reduceIte]
  · have he : 3 * (n.1 : ℤ) + 2 * (-(2 * (n.1 : ℤ)) - 2 * n.2.1 - n.2.2 - 1) +
        2 * (-(n.1 : ℤ) - n.2.1 - n.2.2 - 1) + 3 * (2 * n.2.2 + 2) +
        4 * (n.1 + 2 * n.2.1) = ((n.1 + 2 * n.2.1 + 2 * n.2.2 + 2 : ℕ) : ℤ) := by omega
    have hb : (n.1 : ℤ) + 2 * n.2.1 = ((n.1 + 2 * n.2.1 : ℕ) : ℤ) := by omega
    have hl : (2 * (n.2.2 : ℤ) + 2) / 2 = ((n.2.2 + 1 : ℕ) : ℤ) := by omega
    rw [he, hb, hl]
    simp only [zpow_natCast, pow_add, pow_mul, mul_pow, pow_one]
    ring
  · have he : 3 * (-(n.1 : ℤ) - 1) + 2 * (-0 - 2 * (n.2.1 : ℤ) - n.2.2 - 1) +
        2 * (-0 - (n.2.1 : ℤ) - n.2.2 - 1) + 3 * (2 * n.2.2 + 2) +
        4 * (n.1 + 1 + 2 * n.2.1) = ((n.1 + 1 + 2 * n.2.1 + 2 * n.2.2 + 2 : ℕ) : ℤ) := by omega
    have hb : (n.1 : ℤ) + 1 + 2 * n.2.1 = ((n.1 + 1 + 2 * n.2.1 : ℕ) : ℤ) := by omega
    have hl : (2 * (n.2.2 : ℤ) + 2) / 2 = ((n.2.2 + 1 : ℕ) : ℤ) := by omega
    have hk : -(n.1 : ℤ) - 1 = -((n.1 + 1 : ℕ) : ℤ) := by omega
    rw [he, hb, hl, hk]
    simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_one,
      mul_inv_rev, div_eq_mul_inv, inv_pow]
    ring
end FourierJacobi.Analysis
