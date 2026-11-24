-- Prove2me | solution 1 for Formalism.DivisionValues.ReductionFirst.Tw_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:24.716264+00:00
-- url     : https://prove2.me/submissions/622f3eec-06f7-404b-b3fc-e99b6a598f01

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Matrix
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ReductionFirst
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ReductionFirst
theorem _root_.solution {w : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Tw w) : (s : K) ≠ 0 := by
  intro h
  apply hs.1
  have : s = 0 := RingOfIntegers.ext (by simpa using h)
  rw [this]; exact w.asIdeal.zero_mem
end Formalism.DivisionValues.ReductionFirst
