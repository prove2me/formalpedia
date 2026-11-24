-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.dimension_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:34.158554+00:00
-- url     : https://prove2.me/submissions/552692e5-ca87-4ef4-9505-8c213abf37a9

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sq_sum_fin

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
theorem _root_.solution : DimIdentity := by
  intro a j n0
  have hsq := sq_sum_fin j
  have hd : dimN j n0 = 4 * (∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y)
      + (∑ x, j x ^ 2) + 2 * (∑ x, j x) * n0 := by
    unfold dimN
    have e1 : (∑ x, ∑ y ∈ univ.filter (fun y => x < y), 2 * j x * j y)
        = 2 * ∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y := by
      simp_rw [mul_assoc, ← Finset.mul_sum]
    have e2 : (∑ x, 2 * j x * n0) = 2 * (∑ x, j x) * n0 := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [e1, e2]; ring
  have h1 : (n0 + 2 * ∑ x, j x) ^ 2 = n0 ^ 2 + 2 * (∑ x, j x ^ 2) + 2 * dimN j n0 := by
    rw [hd]
    have : (n0 + 2 * ∑ x, j x) ^ 2 = n0 ^ 2 + 4 * n0 * (∑ x, j x) + 4 * (∑ x, j x) ^ 2 := by ring
    rw [this, hsq]; ring
  refine ⟨h1, ?_, ?_⟩
  · rw [hd]
    have : 2 * (∑ x, j x) * (n0 + 2 * ∑ x, j x) = 2 * (∑ x, j x) * n0 + 4 * (∑ x, j x) ^ 2 := by ring
    rw [this, hsq]
    generalize (∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y) = T
    generalize (∑ x, j x ^ 2) = Q
    generalize 2 * (∑ x, j x) * n0 = R
    omega
  · have h1r : ((n0:ℝ) + 2 * ∑ x, (j x : ℝ)) ^ 2
        = (n0:ℝ) ^ 2 + 2 * (∑ x, (j x : ℝ) ^ 2) + 2 * (dimN j n0 : ℝ) := by exact_mod_cast h1
    linarith
end Formalism.HermitianLatticeCounting.P
