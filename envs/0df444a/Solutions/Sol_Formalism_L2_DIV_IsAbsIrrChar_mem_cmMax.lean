-- Prove2me | solution 1 for Formalism.L2.DIV.IsAbsIrrChar.mem_cmMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:54:52.662536+00:00
-- url     : https://prove2.me/submissions/be1c04b3-b101-4d4f-9a57-30f1a15d300f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_map_inv
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
namespace IsAbsIrrChar
theorem _root_.solution {v0 : InfinitePlace K} (hv : IsConjAt v0) {χ : G → K} (h : IsAbsIrrChar χ)
    (t : G) : χ t ∈ cmMax K := by
  show ∀ σ : K →+* ℂ, σ (star (χ t)) = starRingEnd ℂ (σ (χ t))
  intro σ
  rw [h.star_eq hv t, h.map_inv σ t]
end IsAbsIrrChar
end Formalism.L2.DIV
