-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.matrix_action_evaluation_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:28.330816+00:00
-- url     : https://prove2.me/submissions/f19a7fd4-8bf3-4437-af0a-1e078f43c0cc

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : RankTwoSkewMatrixApply := by
  intro n H e v x
  have key : ∀ w : Fin n → ℂ, ∑ j, herm H (Pi.single j 1) w * x j = herm H x w := by
    intro w
    simp only [herm, dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  ext i
  simp only [rankTwoSkewMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    sub_mul, Finset.sum_sub_distrib]
  rw [← key v, ← key e, Finset.sum_mul, Finset.sum_mul]
  congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring
end Formalism.HermitianLatticeCounting.P
