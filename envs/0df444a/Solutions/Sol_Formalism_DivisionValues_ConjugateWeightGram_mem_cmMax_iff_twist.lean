-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightGram.mem_cmMax_iff_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:59:33.997993+00:00
-- url     : https://prove2.me/submissions/27baac9d-e0a7-4ce8-b989-afb7494790fc

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Theorems.Thm_Formalism_HN_twist


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
open Formalism Formalism.DivisionValues
open RationalHermitianForm
open Formalism.DivisionValues.ConjugateWeightGram
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ConjugateWeightGram
theorem _root_.solution (a : K) : a ∈ cmMax K ↔ ∀ σ : K →+* ℂ, twist σ a = σ a := by
  constructor
  · intro ha σ
    change starRingEnd ℂ (σ (star a)) = σ a
    rw [ha σ, Complex.conj_conj]
  · intro h σ
    have := h σ
    change starRingEnd ℂ (σ (star a)) = σ a at this
    rw [← this, Complex.conj_conj]
end Formalism.DivisionValues.ConjugateWeightGram
