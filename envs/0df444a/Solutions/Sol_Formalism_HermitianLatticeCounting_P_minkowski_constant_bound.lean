-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.minkowski_constant_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:40.693919+00:00
-- url     : https://prove2.me/submissions/07a8350d-6e39-4ee8-bf98-41694beecf67

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : MinkConst := by
  intro f
  have hN : (2 * f).factorial * 2 ^ f ≤ (2 * f) ^ (2 * f) := by
    have h1 : (2 * f).factorial = f.factorial * (f + 1).ascFactorial f := by
      rw [Nat.factorial_mul_ascFactorial]; congr 1; ring
    have h2 : f.factorial ≤ f ^ f := Nat.factorial_le_pow f
    have h3 : (f + 1).ascFactorial f ≤ (f + f) ^ f := Nat.ascFactorial_le_pow_add f f
    calc (2 * f).factorial * 2 ^ f ≤ (f ^ f * (f + f) ^ f) * 2 ^ f := by
          rw [h1]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 h3)
      _ = (2 * f) ^ (2 * f) := by
          rw [two_mul f, pow_add, ← two_mul, mul_pow 2 f f]; ring
  have hR : ((2 * f).factorial : ℝ) * 2 ^ f ≤ ((2 * f : ℕ) : ℝ) ^ (2 * f) := by exact_mod_cast hN
  have hpi := Real.pi_pos
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp
  have hpos : (0 : ℝ) < ((2 * f : ℕ) : ℝ) ^ (2 * f) := by positivity
  rw [div_le_iff₀ hpos, div_pow, div_pow]
  have h4 : (4 : ℝ) ^ f = 2 ^ f * 2 ^ f := by rw [← mul_pow]; norm_num
  rw [h4]
  have hpf : (0 : ℝ) < Real.pi ^ f := by positivity
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpf]
  nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) f]
end Formalism.HermitianLatticeCounting.P
