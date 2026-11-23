-- Prove2me | solution 1 for Formalism.L2.DIV.exists_int_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:28.236616+00:00
-- url     : https://prove2.me/submissions/8b5f7374-7123-4965-8ad1-b4f88610f8d6

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.DIV
theorem _root_.solution {u : K} {n : ℕ} (hn : n ≠ 0) (hu : u ^ n = 1) :
    ∃ b : 𝓞 K, (b : K) = u := by
  have hint : IsIntegral ℤ u :=
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [hu]⟩
  first
  | exact ⟨⟨u, hint⟩, rfl⟩
  | exact ⟨⟨u, (mem_integralClosure_iff ℤ K).mpr hint⟩, rfl⟩
  | exact ⟨NumberField.RingOfIntegers.mk u hint, rfl⟩
end Formalism.L2.DIV
