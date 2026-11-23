-- Prove2me | solution 1 for Formalism.DivisionValues.place_log_sum.vw_nat_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:42.922257+00:00
-- url     : https://prove2.me/submissions/995bd7d5-c313-4670-a685-d3597e0b0036

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundRows
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_WeightedPlaceLogSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.place_log_sum
namespace Formalism.DivisionValues.place_log_sum
theorem _root_.solution {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    0 ≤ vw w (n : K) := by
  have h : ((n : 𝓞 K) : K) = (n : K) := map_natCast _ n
  unfold vw
  rw [← h, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _
end Formalism.DivisionValues.place_log_sum
