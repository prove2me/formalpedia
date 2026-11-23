-- Prove2me | solution 1 for Formalism.L2.DIV.star_mem_cmMax
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:57.198435+00:00
-- url     : https://prove2.me/submissions/250d651a-04db-4a36-a89e-91d8b3f182a7

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
namespace Formalism.L2.DIV
theorem _root_.solution {K : Type} [Field K] [StarRing K] {a : K} (ha : a ∈ cmMax K) :
    star a ∈ cmMax K := by
  have ha' : ∀ σ : K →+* ℂ, σ (star a) = starRingEnd ℂ (σ a) := ha
  show ∀ σ : K →+* ℂ, σ (star (star a)) = starRingEnd ℂ (σ (star a))
  intro σ
  rw [star_star, ha' σ, Complex.conj_conj]
end Formalism.L2.DIV
