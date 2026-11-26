-- Prove2me | solution 1 for FourierJacobi.Analysis.i0_upper_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:19.06746+00:00
-- url     : https://prove2.me/submissions/bfe4a4c3-2f1c-430c-81f7-8abe15f2077c

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Theorems.Thm_FourierJacobi_Analysis_i0UpperRow_cartan
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
theorem _root_.solution (neg : Bool) (t d U V T : ℂ) (e : Fin 2) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0UpperRowEquiv neg (e, n)).val =
      ((1 - t ^ 2) ^ 2 * i0KInitial neg t d V T * (T * V) ^ (e.val + 1) * t ^ 2) *
        (i0KRatio neg t d V T) ^ n.1 * ((T * V) ^ 2 * t ^ 2) ^ n.2.1 *
        (t ^ 2) ^ n.2.2 := by
  unfold i0Shell
  rw [i0UpperRow_cartan]
  cases neg <;> simp only [i0UpperRowEquiv, Equiv.coe_fn_mk, i0KInitial,
    i0KRatio, Bool.false_eq_true, ↓reduceIte]
  · have he : 3 * (n.1 : ℤ) +
        2 * (-(2 * (n.1 : ℤ)) - 2 * n.2.1 - e.val - 1) +
        2 * (-(n.1 : ℤ) - n.2.1 - e.val + n.2.2) +
        3 * 0 + 4 * (n.1 + 2 * n.2.1 + e.val + 1) =
        ((n.1 + 2 * n.2.1 + 2 * n.2.2 + 2 : ℕ) : ℤ) := by omega
    have hb : (n.1 : ℤ) + 2 * n.2.1 + e.val + 1 =
        ((n.1 + 2 * n.2.1 + e.val + 1 : ℕ) : ℤ) := by omega
    rw [he, hb]
    simp only [zero_div, Int.zero_ediv, zpow_zero, pow_zero, mul_one, zpow_natCast, pow_add, pow_mul, mul_pow, pow_one]
    ring
  · have he : 3 * (-(n.1 : ℤ) - 1) +
        2 * (-0 - 2 * (n.2.1 : ℤ) - e.val - 1) +
        2 * (-0 - (n.2.1 : ℤ) - e.val + n.2.2) +
        3 * 0 + 4 * (n.1 + 1 + 2 * n.2.1 + e.val + 1) =
        ((n.1 + 1 + 2 * n.2.1 + 2 * n.2.2 + 2 : ℕ) : ℤ) := by omega
    have hb : (n.1 : ℤ) + 1 + 2 * n.2.1 + e.val + 1 =
        ((n.1 + 1 + 2 * n.2.1 + e.val + 1 : ℕ) : ℤ) := by omega
    have hk : -(n.1 : ℤ) - 1 = -((n.1 + 1 : ℕ) : ℤ) := by omega
    rw [he, hb, hk]
    simp only [zero_div, Int.zero_ediv, zpow_zero, pow_zero, mul_one, zpow_neg, zpow_natCast, pow_add,
      pow_mul, mul_pow, pow_one, mul_inv_rev, div_eq_mul_inv, inv_pow]
    ring
end FourierJacobi.Analysis
