-- Prove2me | solution 1 for Formalism.L2.DIV.subE_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:18.775501+00:00
-- url     : https://prove2.me/submissions/1ff6b6d9-e164-44e7-a03e-c357a6b355ac

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
variable {K : Type} [Field K] [StarRing K] {n : ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution (Z : Submodule K (Fin n → K)) (x : Fin (subDim Z) → K) :
    (subE Z).mulVec x = (((subBasis Z).equivFun.symm x : Z) : Fin n → K) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, subE, Matrix.of_apply, Basis.equivFun_symm_apply,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _
end Formalism.L2.DIV
