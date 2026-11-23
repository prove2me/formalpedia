-- Prove2me | solution 1 for Formalism.DivisionValues.W5.lw_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:25.480102+00:00
-- url     : https://prove2.me/submissions/595bdf31-0242-4e19-bec4-21261b9c0a77

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares

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
open Formalism.DivisionValues.W5
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues.W5
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw w :=
  div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
end Formalism.DivisionValues.W5
