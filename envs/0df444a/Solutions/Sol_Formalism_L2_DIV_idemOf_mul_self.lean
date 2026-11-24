-- Prove2me | solution 1 for Formalism.L2.DIV.idemOf_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:10:56.883832+00:00
-- url     : https://prove2.me/submissions/9b5ea8ef-90ba-4c28-aaa0-1da90a66faeb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_chiIdem_mul

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
open Representation
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.DIV
theorem _root_.solution (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) :
    idemOf X * idemOf X = idemOf X := by
  classical
  unfold idemOf
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [Finset.mul_sum, Finset.sum_congr rfl fun χ' hχ' => chiIdem_mul (hX χ hχ) (hX χ' hχ'),
    Finset.sum_ite_eq, if_pos hχ]
end Formalism.L2.DIV
