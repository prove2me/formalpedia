-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.near_region_product
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:43.29064+00:00
-- url     : https://prove2.me/submissions/87e57717-12e2-45f2-a4f5-7f2e949e1148

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : NearProduct := by
  intro R _ la d n q J f de k hla hde hk hk24 hd hJ hsmall
  rw [← Finset.prod_mul_distrib]
  have h1 : ∀ r, (1 + k * de / la r) ^ (d r * f) * la r ^ (d r * f)
      ≤ Real.exp (k * de * (d r * f : ℕ)) := by
    intro r
    have hl := hla r
    rw [← mul_pow]
    have e : (1 + k * de / la r) * la r = la r + k * de := by
      field_simp [hl.1.ne']
    rw [e, mul_comm (k * de), Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by have := mul_nonneg hk hde; linarith)
    have := Real.add_one_le_exp (k * de)
    linarith
  calc ∏ r, (1 + k * de / la r) ^ (d r * f) * la r ^ (d r * f)
      ≤ ∏ r, Real.exp (k * de * (d r * f : ℕ)) :=
        Finset.prod_le_prod (fun r _ => by
          have h := hla r
          have h2 := div_nonneg (mul_nonneg hk hde) h.1.le
          exact mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg h.1.le _))
          (fun r _ => h1 r)
    _ = Real.exp (k * de * ((∑ r, d r : ℕ) * f)) := by
        rw [← Real.exp_sum, ← Finset.mul_sum]
        congr 2
        push_cast
        rw [Finset.sum_mul]
    _ ≤ Real.exp (48 / 100) := by
        apply Real.exp_le_exp.mpr
        have hd' : ((∑ r, d r : ℕ) : ℝ) ≤ 2 * J * n := by exact_mod_cast hd
        have hJ' : (J:ℝ) ≤ q := by exact_mod_cast hJ
        have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
        have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg _
        calc k * de * ((∑ r, d r : ℕ) * f) ≤ 24 * de * ((2 * q * n) * f) := by
              gcongr
              exact hd'.trans (by gcongr)
          _ = 48 * (de * q * n * f) := by ring
          _ ≤ 48 / 100 := by linarith
    _ ≤ 2 := by
        rw [← Real.le_log_iff_exp_le (by norm_num)]
        have := Real.log_two_gt_d9
        linarith
end Formalism.HermitianLatticeCounting.P
