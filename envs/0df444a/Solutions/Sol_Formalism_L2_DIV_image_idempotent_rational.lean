-- Prove2me | solution 1 for Formalism.L2.DIV.image_idempotent_rational
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:52.155679+00:00
-- url     : https://prove2.me/submissions/d785e1eb-8f5c-4ea9-8b14-c9bddf4bd2eb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_subHasRat_of_span
import Theorems.Thm_Formalism_L2_DIV_subE_rat

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
theorem _root_.solution : ImERat := by
  intro K _ _ n e he i j
  apply subE_rat
  apply subHasRat_of_span _ (Set.range eᵀ) (Matrix.range_mulVecLin e).symm
  rintro v ⟨k, rfl⟩ l
  exact he l k
end Formalism.L2.DIV
