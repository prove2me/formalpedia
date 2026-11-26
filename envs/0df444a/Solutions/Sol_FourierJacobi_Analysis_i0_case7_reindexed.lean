-- Prove2me | solution 1 for FourierJacobi.Analysis.i0_case7_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:21.935689+00:00
-- url     : https://prove2.me/submissions/b8d3aa81-0122-4857-8432-c5c3b1a0d300

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRow_cartan
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0NegativeRowEquiv true n).val =
      ((1 - t ^ 2) ^ 2 * (T * V * t / d) * (T * U * t ^ 4)) *
        (T * V * t / d) ^ n.1 * (t ^ 2) ^ n.2.1 *
          (T * U * t ^ 4) ^ n.2.2 := by
  unfold i0Shell
  rw [i0NegativeRow_cartan]
  simp only [↓reduceIte, i0NegativeRowEquiv_val]
  have he : 3 * (-(n.1 : ℤ) - 1) + 2 * n.2.1 +
      2 * (-(n.2.2 : ℤ) - 1) + 3 * (2 * n.2.2 + 2) + 4 * (n.1 + 1) =
      ((n.1 + 1 + 2 * n.2.1 + 4 * (n.2.2 + 1) : ℕ) : ℤ) := by omega
  have hk : -(n.1 : ℤ) - 1 = -((n.1 + 1 : ℕ) : ℤ) := by omega
  have hb : (n.1 : ℤ) + 1 = ((n.1 + 1 : ℕ) : ℤ) := by omega
  have hl : (2 * (n.2.2 : ℤ) + 2) / 2 = ((n.2.2 + 1 : ℕ) : ℤ) := by omega
  rw [he, hk, hb, hl]
  simp only [zpow_neg, zpow_natCast, pow_add, pow_mul, mul_pow, pow_one,
    mul_inv_rev, div_eq_mul_inv, inv_pow]
  ring
end FourierJacobi.Analysis
