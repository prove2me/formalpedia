-- Prove2me | solution 1 for Formalism.L2.DIV.Test.aug_idemOf_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:54:53.420796+00:00
-- url     : https://prove2.me/submissions/0de58165-352d-44c0-b978-5e13602ad33f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_Test_idemOf_one_coeff
import Theorems.Thm_Formalism_L2_DIV_Test_aug_eq_sum

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
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
namespace Formalism.L2.DIV.Test
theorem _root_.solution : aug K G (idemOf ({fun _ : G => (1 : K)} : Finset (G → K))) = 1 := by
  rw [aug_eq_sum]
  simp only [idemOf_one_coeff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [one_div, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
end Formalism.L2.DIV.Test
