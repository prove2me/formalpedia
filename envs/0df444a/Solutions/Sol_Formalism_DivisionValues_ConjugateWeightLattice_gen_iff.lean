-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightLattice.gen_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:25:57.066247+00:00
-- url     : https://prove2.me/submissions/13e05624-71d0-4966-aa46-9a1205699165

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ConjugateWeightLattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ConjugateWeightLattice
theorem _root_.solution (p : Ideal (𝓞 K)) (s : 𝓞 K) :
    (s ∉ p ∧ ∀ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s) → t ∉ p) ↔
      (s ∉ p ∧ cO K s ∉ p) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 _ rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t ht => ?_⟩
    have : t = cO K s := RingOfIntegers.ext ht
    rw [this]
    exact h2
end Formalism.DivisionValues.ConjugateWeightLattice
