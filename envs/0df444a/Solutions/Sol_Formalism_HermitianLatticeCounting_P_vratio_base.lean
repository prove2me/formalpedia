-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.vratio_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:43.166984+00:00
-- url     : https://prove2.me/submissions/8c0137cd-e80f-4028-aa39-62e1d4b20136

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
theorem _root_.solution (p q k : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    2 * Real.pi ^ p / (k.factorial : ℝ) * (2 * Real.pi ^ q)
      ≤ (2 * Real.pi * Real.exp 1) ^ (p + q) * ((2 * Real.pi * Real.exp 1) / (p:ℝ)) ^ k := by
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hC1 : 1 ≤ 2 * Real.pi * Real.exp 1 := by nlinarith
  have h1 := Real.pow_div_factorial_le_exp (p:ℝ) hp0.le k
  have hk0 : (0:ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h2 : 1 / (k.factorial:ℝ) ≤ Real.exp p / (p:ℝ)^k := by
    rw [div_le_div_iff₀ hk0 (by positivity)]
    rw [div_le_iff₀ hk0] at h1
    linarith
  have h3 : 1 / (p:ℝ)^k ≤ ((2 * Real.pi * Real.exp 1) / (p:ℝ)) ^ k := by
    rw [div_pow]
    gcongr
    exact one_le_pow₀ hC1
  have h4 : 4 * Real.pi ^ (p+q) * Real.exp p ≤ (2 * Real.pi * Real.exp 1) ^ (p + q) := by
    rw [mul_pow, mul_pow]
    have a : (4:ℝ) ≤ 2^(p+q) := by
      calc (4:ℝ) = 2^2 := by norm_num
        _ ≤ 2^(p+q) := pow_le_pow_right₀ (by norm_num) (by omega)
    have b : Real.exp p ≤ Real.exp 1 ^ (p+q) := by
      rw [← Real.exp_nat_mul, mul_one]; apply Real.exp_le_exp.mpr; push_cast
      linarith [(Nat.cast_nonneg q : (0:ℝ) ≤ q)]
    gcongr
  calc 2 * Real.pi ^ p / (k.factorial : ℝ) * (2 * Real.pi ^ q)
      = 4 * Real.pi^(p+q) * (1 / (k.factorial:ℝ)) := by rw [pow_add]; ring
    _ ≤ 4 * Real.pi^(p+q) * (Real.exp p / (p:ℝ)^k) := by gcongr
    _ = (4 * Real.pi^(p+q) * Real.exp p) * (1 / (p:ℝ)^k) := by ring
    _ ≤ _ := by gcongr
end Formalism.HermitianLatticeCounting.P
