-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.factorial_mul_two_pow_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:14.482835+00:00
-- url     : https://prove2.me/submissions/8d46f0c7-160e-40d4-a6f0-5d05830a4f33

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Theorems.Thm_Formalism_SLP_P_base


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (d : ℕ) (hd : 1 ≤ d) : (d.factorial : ℝ) * 2 ^ (d - 1) ≤ (d : ℝ) ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    have hd' : (0:ℝ) < d := by exact_mod_cast hd
    have hinv : (0:ℝ) ≤ 1 / d := by positivity
    have h1 : 1 + (d:ℝ) * (1 / d) ≤ (1 + 1 / d) ^ d := one_add_mul_le_pow (by linarith) d
    have h2 : (1:ℝ) + d * (1 / d) = 2 := by field_simp; ring
    have h3 : ((d:ℝ) + 1) ^ d = (1 + 1 / d) ^ d * (d:ℝ) ^ d := by
      rw [← mul_pow]; congr 1; field_simp
    have hb : (2:ℝ) * (d:ℝ) ^ d ≤ ((d:ℝ) + 1) ^ d := by
      rw [h3]; rw [h2] at h1; nlinarith [pow_pos hd' d]
    have e1 : d + 1 - 1 = (d - 1) + 1 := by omega
    rw [Nat.factorial_succ, e1, pow_succ]
    push_cast
    calc ((d:ℝ) + 1) * (d.factorial : ℝ) * (2 ^ (d - 1) * 2)
        = ((d:ℝ) + 1) * 2 * ((d.factorial : ℝ) * 2 ^ (d - 1)) := by ring
      _ ≤ ((d:ℝ) + 1) * 2 * (d:ℝ) ^ d := by gcongr
      _ = ((d:ℝ) + 1) * (2 * (d:ℝ) ^ d) := by ring
      _ ≤ ((d:ℝ) + 1) * ((d:ℝ) + 1) ^ d := by gcongr
      _ = ((d:ℝ) + 1) ^ (d + 1) := by ring
end Formalism.HermitianLatticeCounting.P
