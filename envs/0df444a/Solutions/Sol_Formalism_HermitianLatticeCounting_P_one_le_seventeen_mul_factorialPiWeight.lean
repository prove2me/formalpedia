-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.one_le_seventeen_mul_factorialPiWeight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:51.180048+00:00
-- url     : https://prove2.me/submissions/3957d181-1db9-4ca4-94d6-007809b2e678

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_piPowDivFactorialLt

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
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (v : ℝ) (hv : 1 ≤ v) (k : ℕ) (hk : 3 ≤ k) : 1 ≤ 17 * s5bA v (k - 1) := by
  have h := piPowDivFactorialLt k hk
  have hπ := Real.pi_pos
  have hF : (0:ℝ) < ((k - 2).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  unfold s5bA
  rw [show k - 1 - 1 = k - 2 by omega]
  have hv' : (1 / Real.pi) ^ (k - 1) ≤ (v / Real.pi) ^ (k - 1) :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hv hπ.le) _
  rw [div_lt_iff₀ hF] at h
  have e : (1 / Real.pi) ^ (k - 1) = (Real.pi ^ (k - 1))⁻¹ := by rw [one_div, inv_pow]
  rw [e] at hv'
  have hpk : 0 < Real.pi ^ (k - 1) := pow_pos hπ _
  calc (1:ℝ) = (Real.pi ^ (k - 1))⁻¹ * Real.pi ^ (k - 1) := (inv_mul_cancel₀ hpk.ne').symm
    _ ≤ (Real.pi ^ (k - 1))⁻¹ * (17 * ((k - 2).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left h.le (inv_nonneg.mpr hpk.le)
    _ ≤ (v / Real.pi) ^ (k - 1) * (17 * ((k - 2).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hv' (by positivity)
    _ = 17 * (((k - 2).factorial : ℝ) * (v / Real.pi) ^ (k - 1)) := by ring
end Formalism.HermitianLatticeCounting.P
