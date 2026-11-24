-- Prove2me | solution 1 for Formalism.L2.DIV.chiIdem_selfAdj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:55:26.511802+00:00
-- url     : https://prove2.me/submissions/7a1e5319-924c-4561-b115-7888e8dce9fe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_gaStar_single
import Theorems.Thm_Formalism_L2_DIV_gaStar_sum
import Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_star_eq

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
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.DIV
theorem _root_.solution {v0 : InfinitePlace K} (hv : IsConjAt v0) {χ : G → K} (h : IsAbsIrrChar χ) :
    gaStar (chiIdem χ) = chiIdem χ := by
  unfold chiIdem
  rw [gaStar_sum]
  simp only [gaStar_single]
  rw [← Equiv.sum_comp (Equiv.inv G)]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Equiv.inv_apply, inv_inv]
  congr 1
  rw [star_mul', star_div₀, star_natCast, h.star_eq hv, h.star_eq hv, inv_one]
end Formalism.L2.DIV
