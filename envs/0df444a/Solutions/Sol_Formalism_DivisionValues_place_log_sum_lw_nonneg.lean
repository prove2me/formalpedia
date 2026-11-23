-- Prove2me | solution 1 for Formalism.DivisionValues.place_log_sum.lw_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:42.242623+00:00
-- url     : https://prove2.me/submissions/d7af27a2-63e6-43a2-97fd-16c688bb8994

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw w :=
  div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
end Formalism.DivisionValues.place_log_sum
