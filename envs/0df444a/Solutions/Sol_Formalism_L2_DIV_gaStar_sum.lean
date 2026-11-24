-- Prove2me | solution 1 for Formalism.L2.DIV.gaStar_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:23:50.983482+00:00
-- url     : https://prove2.me/submissions/5bfb197e-ee76-432c-9d00-82fc407936fc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_gaStar_add
import Theorems.Thm_Formalism_L2_DIV_gaStar_zero

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
theorem _root_.solution [StarRing K] {ι : Type} (s : Finset ι) (f : ι → MonoidAlgebra K G) :
    gaStar (∑ i ∈ s, f i) = ∑ i ∈ s, gaStar (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact gaStar_zero
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, gaStar_add, ih]
end Formalism.L2.DIV
