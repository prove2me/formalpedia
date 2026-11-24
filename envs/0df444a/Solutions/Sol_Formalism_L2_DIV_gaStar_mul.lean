-- Prove2me | solution 1 for Formalism.L2.DIV.gaStar_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:55:30.650924+00:00
-- url     : https://prove2.me/submissions/6a0ce5fa-055d-49f1-a800-7f4a47d6cfae

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_eq_sum_single
import Theorems.Thm_Formalism_L2_DIV_gaStar_single
import Theorems.Thm_Formalism_L2_DIV_gaStar_sum

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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.DIV
theorem _root_.solution [StarRing K] (a b : MonoidAlgebra K G) : gaStar (a * b) = gaStar b * gaStar a := by
  classical
  conv_lhs => rw [eq_sum_single a, eq_sum_single b]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, gaStar_sum, MonoidAlgebra.single_mul_single, gaStar_single, mul_inv_rev,
    star_mul']
  conv_rhs =>
    unfold gaStar
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, MonoidAlgebra.single_mul_single]
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [mul_comm (star (a.coeff s))]
end Formalism.L2.DIV
