-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.farA_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:45.453484+00:00
-- url     : https://prove2.me/submissions/9eb0d0c5-5af1-4e10-92f7-64377b42408b

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_exp_neg_one_le_half

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
theorem _root_.solution {B h ε : ℝ} (hε : 0 < ε) (h32 : 32 * B ≤ h * ε) (h16 : 16 ≤ h * ε ^ 2) (k : ℕ) :
    farA B h ε (k+1) ≤ Real.exp (-(h * ε ^ 2 / 16)) * (1 / 2) ^ k := by
  have h1 : Real.exp (-(h * ε ^ 2 / 16)) * Real.exp (-1) ^ k
      ≤ Real.exp (-(h * ε ^ 2 / 16)) * (1 / 2) ^ k := by
    have := exp_neg_one_le_half
    have h0 := (Real.exp_pos (-1)).le
    gcongr
  refine le_trans ?_ h1
  unfold farA farW
  rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hP : (k:ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self (n := k)
  have hB : 2 * (B * ε) ≤ h * ε ^ 2 / 16 := by nlinarith
  have e : B * (2 ^ (k+1) * ε) + -(h / 8 * (ε * (2 ^ k * ε)))
      = 2 ^ k * (2 * (B * ε) - 2 * (h * ε ^ 2 / 16)) := by ring
  rw [e]
  have hT : 1 ≤ h * ε ^ 2 / 16 := by linarith
  generalize h * ε ^ 2 / 16 = T at *
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have h2 : (2:ℝ) ^ k * (2 * (B * ε) - 2 * T) ≤ 2 ^ k * (-T) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : ((k:ℝ) + 1) * T ≤ 2 ^ k * T := by gcongr
  nlinarith
end Formalism.HermitianLatticeCounting.P
