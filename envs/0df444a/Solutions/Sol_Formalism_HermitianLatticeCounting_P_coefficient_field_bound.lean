-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.coefficient_field_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:22.99255+00:00
-- url     : https://prove2.me/submissions/74545e91-d8cb-425b-9802-8f817943825e

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Theorems.Thm_Formalism_SLP_Final_omegaPow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.CfBound := by
  intro f x k hf hx
  have hx1 : (1:ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0:ℝ) < x := by linarith
  have h1 := Formalism.SLP.Final.omegaPow (2 * f) x (by omega) hx
  have e : (((2 * f : ℕ) : ℝ)) = 2 * (f : ℝ) := by push_cast; ring
  rw [e] at h1 ⊢
  calc (2 * (f:ℝ)) ^ (Nat.primeFactorsList x).length * (x : ℝ) ^ k
      ≤ (x : ℝ) ^ Real.logb 2 (2 * f) * (x : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (x : ℝ) ^ ((k : ℝ) + Real.logb 2 (2 * f)) := by
        rw [Real.rpow_add hx0, Real.rpow_natCast, mul_comm]
    _ ≤ (x : ℝ) ^ ((k : ℝ) + (1 + Real.logb 2 (2 * f))) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
end Formalism.HermitianLatticeCounting.P
