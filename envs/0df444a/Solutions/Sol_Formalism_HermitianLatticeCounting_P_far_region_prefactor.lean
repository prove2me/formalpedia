-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.far_region_prefactor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:46.169169+00:00
-- url     : https://prove2.me/submissions/0e334883-73e6-4349-a459-32c6953ddff9

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
theorem _root_.solution : FarPrefactor := by
  intro n f τs hn hf hτ hnτ
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hss : Real.sqrt (n:ℝ) ^ 2 = n := Real.sq_sqrt (by linarith)
  have hfm : f ≤ n ^ 2 * f := Nat.le_mul_of_pos_left _ (by positivity)
  have e1 : (3 * Real.sqrt n / τs ^ 2) ^ (2 * n ^ 2 * f) = (9 * n / τs ^ 4) ^ (n ^ 2 * f) := by
    rw [mul_assoc 2, pow_mul]
    congr 1
    rw [div_pow, mul_pow, hss]; ring
  have e2 : (3 / τs) ^ (5 * n ^ 2 * f) = (243 / τs ^ 5) ^ (n ^ 2 * f) := by
    rw [mul_assoc 5, pow_mul]
    congr 1
    rw [div_pow]; norm_num
  rw [e1, e2]
  calc (9 * (n:ℝ) / τs ^ 4) ^ (n ^ 2 * f) * 4 ^ f
      ≤ (9 * (n:ℝ) / τs ^ 4) ^ (n ^ 2 * f) * 4 ^ (n ^ 2 * f) := by
        gcongr
        · norm_num
    _ = (9 * (n:ℝ) / τs ^ 4 * 4) ^ (n ^ 2 * f) := (mul_pow _ _ _).symm
    _ ≤ (243 / τs ^ 5) ^ (n ^ 2 * f) := by
        apply pow_le_pow_left₀ (by positivity)
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have : 9 * (n:ℝ) * 4 * τs ^ 5 = 36 * (n * τs) * τs ^ 4 := by ring
        rw [this]
        have h4 : 0 < τs ^ 4 := by positivity
        nlinarith
end Formalism.HermitianLatticeCounting.P
