-- Prove2me | solution 1 for FourierJacobi.Algebra.weyl_polynomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:00.335536+00:00
-- url     : https://prove2.me/submissions/7f17da53-63b5-45e1-9494-503f43a78a06

import Definitions.Def_FourierJacobi_Algebra_WeylCoefficient10
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Theorems.Thm_FourierJacobi_Algebra_clearedExpansion
import Theorems.Thm_FourierJacobi_Algebra_coefficientIdentity

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b d : K) :
    (∑ i : Fin 8, weylClearedTerms t a b d i) = weylTargetNumerator t a b d := by
  simp_rw [clearedExpansion, evalCoefficients]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, coefficientIdentity]
  have ht : weylTargetNumerator t a b d = weylTargetCoefficient t a b * d ^ 5 := by
    unfold weylTargetNumerator weylTargetCoefficient
    ac_rfl
  rw [ht]
  norm_num [Fin.sum_univ_succ]
end FourierJacobi.Algebra
