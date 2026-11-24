-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5a4_geo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:48.237612+00:00
-- url     : https://prove2.me/submissions/507dc788-fcb5-45ec-92ab-087305e17f1b

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
theorem _root_.solution (n : ℕ) : HasSum (fun i : ℕ => (((n : ℝ) + 2) ^ (i + 2))⁻¹)
    (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := by
  have hr0 : (0 : ℝ) ≤ ((n : ℝ) + 2)⁻¹ := by positivity
  have hr1 : ((n : ℝ) + 2)⁻¹ < 1 := by
    apply inv_lt_one_of_one_lt₀; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ((((n : ℝ) + 2)⁻¹) ^ 2)
  have e1 : (fun i : ℕ => (((n : ℝ) + 2) ^ (i + 2))⁻¹) =
      fun i : ℕ => (((n : ℝ) + 2)⁻¹) ^ 2 * (((n : ℝ) + 2)⁻¹) ^ i := by
    ext i; rw [← pow_add, inv_pow, add_comm 2 i]
  have e2 : 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) =
      (((n : ℝ) + 2)⁻¹) ^ 2 * (1 - ((n : ℝ) + 2)⁻¹)⁻¹ := by
    have h1 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h3 : (1 - ((n : ℝ) + 2)⁻¹) = ((n : ℝ) + 1) / ((n : ℝ) + 2) := by field_simp; ring
    rw [h3]; field_simp
  rw [e1, e2]; exact h
end Formalism.HermitianLatticeCounting.P
