-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.TableLargeAssembly
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:23:57.803485+00:00
-- url     : https://prove2.me/submissions/c0f48943-d9be-4371-afb5-efd668957d7e

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Theorems.Thm_ExplicitPNT_dusart_refined_psi_error_of_zero_free_region
import Theorems.Thm_ExplicitPNT_kadiri_zero_free_region_569693
import Definitions.Def_DusartThetaTable1Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0010
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_seven_eighths_lt_re
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Definitions.Def_dusart_psi_433_20261014_PsiComparison
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_TableLargeRows

set_option autoImplicit false
set_option maxHeartbeats 1000000
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem row_3000 : ∀ (x : ℝ) (hx : Real.exp 3000 ≤ x),
    |Chebyshev.psi x - x| ≤ (3156 / 10^16 : ℝ) * x :=
  ExplicitPNT.DusartTable1.Modules.TableLargeRows.2.2.2.1

private theorem row_3500 : ∀ (x : ℝ) (hx : Real.exp 3500 ≤ x),
    |Chebyshev.psi x - x| ≤ (1116 / 10^16 : ℝ) * x :=
  ExplicitPNT.DusartTable1.Modules.TableLargeRows.2.2.2.2.1

private theorem row_4000 : ∀ (x : ℝ) (hx : Real.exp 4000 ≤ x),
    |Chebyshev.psi x - x| ≤ (3946 / 10^17 : ℝ) * x :=
  ExplicitPNT.DusartTable1.Modules.TableLargeRows.2.2.2.2.2.1

private theorem row_4500 : ∀ (x : ℝ) (hx : Real.exp 4500 ≤ x),
    |Chebyshev.psi x - x| ≤ (1274 / 10^17 : ℝ) * x :=
  ExplicitPNT.DusartTable1.Modules.TableLargeRows.2.2.2.2.2.2.1

private theorem row_5000 : ∀ (x : ℝ) (hx : Real.exp 5000 ≤ x),
    |Chebyshev.psi x - x| ≤ (3956 / 10^18 : ℝ) * x :=
  ExplicitPNT.DusartTable1.Modules.TableLargeRows.2.2.2.2.2.2.2.1

private theorem row_6000 : ∀ (x : ℝ) (hx : Real.exp 6000 ≤ x),
    |Chebyshev.psi x - x| ≤ (4893 / 10^19 : ℝ) * x :=
  ExplicitPNT.DusartTable1.Modules.TableLargeRows.2.2.2.2.2.2.2.2.1

private theorem row_7000 : ∀ (x : ℝ) (hx : Real.exp 7000 ≤ x),
    |Chebyshev.psi x - x| ≤ (6393 / 10^20 : ℝ) * x :=
  ExplicitPNT.DusartTable1.Modules.TableLargeRows.2.2.2.2.2.2.2.2.2.1

private theorem row_8000 : ∀ (x : ℝ) (hx : Real.exp 8000 ≤ x),
    |Chebyshev.psi x - x| ≤ (8969 / 10^21 : ℝ) * x :=
  ExplicitPNT.DusartTable1.Modules.TableLargeRows.2.2.2.2.2.2.2.2.2.2.1

private theorem row_9000 : ∀ (x : ℝ) (hx : Real.exp 9000 ≤ x),
    |Chebyshev.psi x - x| ≤ (2427 / 10^21 : ℝ) * x :=
  ExplicitPNT.DusartTable1.Modules.TableLargeRows.2.2.2.2.2.2.2.2.2.2.2

private theorem all_large_rows
    (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (hb : 3000 ≤ r.b) (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x := by
  simp only [DusartThetaTable.rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst r
  all_goals try { norm_num at hb }
  all_goals first
    | (convert row_3000 x hx using 1 <;> norm_num)
    | (convert row_3500 x hx using 1 <;> norm_num)
    | (convert row_4000 x hx using 1 <;> norm_num)
    | (convert row_4500 x hx using 1 <;> norm_num)
    | (convert row_5000 x hx using 1 <;> norm_num)
    | (convert row_6000 x hx using 1 <;> norm_num)
    | (convert row_7000 x hx using 1 <;> norm_num)
    | (convert row_8000 x hx using 1 <;> norm_num)
    | (convert row_9000 x hx using 1 <;> norm_num)

private theorem row_epsilon_minimum (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows) :
    (2427 / 10 ^ 21 : ℝ) ≤ (r.epsilon : ℝ) := by
  simp only [DusartThetaTable.rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst r <;> norm_num

private theorem all_rows_above_exp9000
    (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (x : ℝ) (hx : Real.exp 9000 ≤ x) :
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x := by
  exact (row_9000 x hx).trans
    (mul_le_mul_of_nonneg_right (row_epsilon_minimum r hr)
      ((Real.exp_pos 9000).trans_le hx).le)

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (hb : 3000 ≤ r.b) (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x),
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x
) ∧
(
    ∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows),
    (2427 / 10 ^ 21 : ℝ) ≤ (r.epsilon : ℝ)
) ∧
(
    ∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (x : ℝ) (hx : Real.exp 9000 ≤ x),
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x
) := by
  exact ⟨all_large_rows, row_epsilon_minimum, all_rows_above_exp9000⟩
