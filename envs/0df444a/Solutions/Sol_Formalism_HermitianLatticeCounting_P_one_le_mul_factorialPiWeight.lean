-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.one_le_mul_factorialPiWeight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:23.380548+00:00
-- url     : https://prove2.me/submissions/6944fcbc-833f-4cdc-b16c-5e2237e0340b

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_invFactorialLeStirling

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
theorem _root_.solution (v : ℝ) (hv : 1 ≤ v) (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ (Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)) * s5bA v k := by
  have hst := invFactorialLeStirling k hk
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hv0 : 0 < v := by linarith
  have hπ0 : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hk0' : (k:ℝ) ≠ 0 := hk0.ne'
  have hv0' : v ≠ 0 := hv0.ne'
  have hF : (0:ℝ) < ((k - 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  unfold s5bA
  have e0 : (Real.exp 1 / k) ^ k = (Real.exp 1 * Real.pi / (k * v)) ^ k * (v / Real.pi) ^ k := by
    rw [← mul_pow]; congr 1
    first | (field_simp; ring) | field_simp
  have e : (Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)) *
      (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) =
      ((Real.exp 1 / k) ^ k * Real.sqrt (k / (2 * Real.pi))) * ((k - 1).factorial : ℝ) := by
    rw [e0]; ring
  rw [e]
  exact (div_le_iff₀ hF).mp hst
end Formalism.HermitianLatticeCounting.P
