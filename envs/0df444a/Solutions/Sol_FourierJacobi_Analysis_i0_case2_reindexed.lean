-- Prove2me | solution 1 for FourierJacobi.Analysis.i0_case2_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:14.441838+00:00
-- url     : https://prove2.me/submissions/47bf58ac-0cbe-4111-8968-781e2da83966

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Theorems.Thm_FourierJacobi_Analysis_i0PositiveRow_cartan

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
namespace FourierJacobi.Analysis
theorem _root_.solution (t d U V T : ℂ) (n : ℕ × ℕ × ℕ) :
    i0Shell t d U V T (i0PositiveRowEquiv true n).val =
      ((1 - t ^ 2) ^ 2 * (T * U * t ^ 4)) *
        (d * T * V * t) ^ n.1 * (t ^ 2) ^ n.2.1 *
          (T * U * t ^ 4) ^ n.2.2 := by
  unfold i0Shell
  rw [i0PositiveRow_cartan]
  simp only [↓reduceIte, i0PositiveRowEquiv_val]
  have he : 3 * (n.1 : ℤ) + 2 * ((n.2.1 : ℤ) - 2 * n.1) +
      2 * (-(n.1 : ℤ) - n.2.2 - 1) + 3 * (2 * n.2.2 + 2) + 4 * n.1 =
      ((n.1 + 2 * n.2.1 + 4 * (n.2.2 + 1) : ℕ) : ℤ) := by omega
  have hl : (2 * (n.2.2 : ℤ) + 2) / 2 = ((n.2.2 + 1 : ℕ) : ℤ) := by omega
  rw [he, hl]
  simp only [zpow_natCast, pow_add, pow_mul, mul_pow, pow_one]
  ring
end FourierJacobi.Analysis
