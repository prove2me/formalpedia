-- Prove2me | solution 1 for Formalism.L2.DIV.idemOf_central
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:10:58.369279+00:00
-- url     : https://prove2.me/submissions/d8877eee-6193-4706-877d-0dc90e0cffc9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_eq_sum_single
import Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_conj
import Theorems.Thm_Formalism_L2_DIV_chiIdem_comm_single

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
theorem _root_.solution (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (b : MonoidAlgebra K G) :
    b * idemOf X = idemOf X * b := by
  rw [eq_sum_single b, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold idemOf
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun χ hχ => chiIdem_comm_single (hX χ hχ).conj s _
end Formalism.L2.DIV
