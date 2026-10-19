-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.TableMiddleRows
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:38:02.779087+00:00
-- url     : https://prove2.me/submissions/e8931f8b-903a-4d0a-ac51-cfded4b1b3f6

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
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterPsi
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_TableLargeAssembly

set_option autoImplicit false
set_option maxHeartbeats 1000000
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem psi_exp_power_bound : ∀ (t : ℝ) (ht : 300 ≤ t),
    |Chebyshev.psi (Real.exp t) - Real.exp t| ≤ 140 * Real.exp (9 * t / 10) :=
  ExplicitPNT.DusartTable1.Modules.PowerQuarterPsi.2.2

private theorem row_epsilon_minimum : ∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows),
    (2427 / 10 ^ 21 : ℝ) ≤ (r.epsilon : ℝ) :=
  ExplicitPNT.DusartTable1.Modules.TableLargeAssembly.2.1

private theorem psi_of_power_certificate (b : ℝ) (q : ℕ) (ε : ℝ) (hq : 30 ≤ q)
    (hqb : (q : ℝ) ≤ b / 10) (hε : 0 ≤ ε)
    (hnum : (140 : ℝ) ≤ ε * (2718281828 / 10^9 : ℝ)^q)
    (x : ℝ) (hx : Real.exp b ≤ x) : |Chebyshev.psi x - x| ≤ ε * x := by
  have hx0 := (Real.exp_pos b).trans_le hx
  have hlog : b ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos b) hx
    simpa only [Real.log_exp] using h
  have hqR : (30 : ℝ) ≤ q := by exact_mod_cast hq
  have hqt : (q : ℝ) ≤ Real.log x / 10 := by linarith
  have hp := psi_exp_power_bound (Real.log x) (by linarith)
  rw [Real.exp_log hx0] at hp
  have hpow : (2718281828 / 10^9 : ℝ)^q ≤ Real.exp (q : ℝ) := by
    have he : (2718281828 / 10^9 : ℝ) ≤ Real.exp 1 := by
      have h := Real.exp_one_gt_d9
      norm_num at h ⊢
      linarith
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718281828 / 10^9) he q
    simpa only [← Real.exp_nat_mul, mul_one] using hh
  have hn : (140 : ℝ) ≤ ε * Real.exp (Real.log x / 10) :=
    hnum.trans (mul_le_mul_of_nonneg_left
      (hpow.trans (Real.exp_le_exp.mpr hqt)) hε)
  apply hp.trans
  calc
    140 * Real.exp (9 * Real.log x / 10) ≤
      (ε * Real.exp (Real.log x / 10)) * Real.exp (9 * Real.log x / 10) :=
        mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
    _ = ε * x := by
      rw [mul_assoc, ← Real.exp_add,
        show Real.log x / 10 + 9 * Real.log x / 10 = Real.log x by ring,
        Real.exp_log hx0]

private theorem row_300 (x : ℝ) (hx : Real.exp 300 ≤ x) :
    |Chebyshev.psi x - x| ≤ (1404 / 10^14 : ℝ) * x := by
  exact psi_of_power_certificate 300 30 (1404 / 10^14)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx

private theorem row_400 (x : ℝ) (hx : Real.exp 400 ≤ x) :
    |Chebyshev.psi x - x| ≤ (1288 / 10^14 : ℝ) * x := by
  exact psi_of_power_certificate 400 40 (1288 / 10^14)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx

private theorem all_rows_above_exp500
    (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (x : ℝ) (hx : Real.exp 500 ≤ x) :
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x := by
  have hp := psi_of_power_certificate 500 50 (2427 / 10^21)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) x hx
  exact hp.trans (mul_le_mul_of_nonneg_right (row_epsilon_minimum r hr)
    ((Real.exp_pos 500).trans_le hx).le)

private theorem all_rows_ge300
    (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (hb : 300 ≤ r.b) (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x) :
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x := by
  by_cases h500 : 500 ≤ r.b
  · apply all_rows_above_exp500 r hr x
    exact (Real.exp_le_exp.mpr (by exact_mod_cast h500)).trans hx
  · simp only [DusartThetaTable.rows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst r
    all_goals try { norm_num at hb }
    all_goals try { norm_num at h500 }
    all_goals first
      | (convert row_300 x hx using 1 <;> norm_num)
      | (convert row_400 x hx using 1 <;> norm_num)

private theorem all_rows_on_target_domain_above_exp300
    (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x) (h300 : Real.exp 300 ≤ x) :
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x := by
  by_cases hb : 300 ≤ r.b
  · exact all_rows_ge300 r hr hb x hx
  · have hε : (1404 / 10^14 : ℝ) ≤ (r.epsilon : ℝ) := by
      simp only [DusartThetaTable.rows, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        subst r
      all_goals try { norm_num at hb }
      all_goals norm_num
    exact (row_300 x h300).trans (mul_le_mul_of_nonneg_right hε
      ((Real.exp_pos 300).trans_le h300).le)

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (b : ℝ) (q : ℕ) (ε : ℝ) (hq : 30 ≤ q)
    (hqb : (q : ℝ) ≤ b / 10) (hε : 0 ≤ ε)
    (hnum : (140 : ℝ) ≤ ε * (2718281828 / 10^9 : ℝ)^q)
    (x : ℝ) (hx : Real.exp b ≤ x),
    |Chebyshev.psi x - x| ≤ ε * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 300 ≤ x),
    |Chebyshev.psi x - x| ≤ (1404 / 10^14 : ℝ) * x
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 400 ≤ x),
    |Chebyshev.psi x - x| ≤ (1288 / 10^14 : ℝ) * x
) ∧
(
    ∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (x : ℝ) (hx : Real.exp 500 ≤ x),
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x
) ∧
(
    ∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (hb : 300 ≤ r.b) (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x),
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x
) ∧
(
    ∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (x : ℝ) (hx : Real.exp (r.b : ℝ) ≤ x) (h300 : Real.exp 300 ≤ x),
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x
) := by
  exact ⟨psi_of_power_certificate, row_300, row_400, all_rows_above_exp500, all_rows_ge300, all_rows_on_target_domain_above_exp300⟩
