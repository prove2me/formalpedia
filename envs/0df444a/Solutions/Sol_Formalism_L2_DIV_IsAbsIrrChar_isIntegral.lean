-- Prove2me | solution 1 for Formalism.L2.DIV.IsAbsIrrChar.isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:10:26.131277+00:00
-- url     : https://prove2.me/submissions/de7271ca-2242-4043-afe4-742a0fa4d72a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_trace_isIntegral_of_pow_eq_one

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
namespace IsAbsIrrChar
theorem _root_.solution {χ : G → K} (h : IsAbsIrrChar χ) (t : G) : IsIntegral ℤ (χ t) := by
  obtain ⟨n, ρ, -, hχ⟩ := h
  have hpow : (ρ t) ^ Fintype.card G = 1 := by rw [← map_pow, pow_card_eq_one, map_one]
  have h1 := trace_isIntegral_of_pow_eq_one (ρ t) Fintype.card_ne_zero hpow
  have h2 : IsIntegral ℤ (algebraMap K (AlgebraicClosure K) (χ t)) := by
    rw [← hχ t]
    exact h1
  exact (isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure K)).injective).mp h2
end IsAbsIrrChar
end Formalism.L2.DIV
