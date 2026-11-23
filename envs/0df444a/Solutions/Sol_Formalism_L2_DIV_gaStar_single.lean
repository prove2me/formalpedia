-- Prove2me | solution 1 for Formalism.L2.DIV.gaStar_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:34.333904+00:00
-- url     : https://prove2.me/submissions/8a7f13f7-8738-4b2a-b438-c13a753ae5c4

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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.DIV
theorem _root_.solution [StarRing K] (t : G) (x : K) :
    gaStar (MonoidAlgebra.single t x) = MonoidAlgebra.single t⁻¹ (star x) := by
  classical
  unfold gaStar
  rw [Finset.sum_eq_single t]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  · intro u _ hu
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hu), star_zero,
      MonoidAlgebra.single_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h
end Formalism.L2.DIV
