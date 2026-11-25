-- Prove2me | solution 1 for Formalism.DivisionValues.eigen_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:23.642061+00:00
-- url     : https://prove2.me/submissions/82d1e919-29a0-4022-8bda-9894de8d9868

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_full_eigen_commuting
import Theorems.Thm_Formalism_DivisionValues_commuting_twist

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
namespace Formalism.DivisionValues
theorem _root_.solution : EigenTwist := by
  intro K _ _ _ K0 hK0 v0 hv0 n H hH hpos 𝒯 h𝒯 hcomm hadj Z Ω _ j hZ σ
  exact commuting_twist K K0 hK0 v0 hv0 n H hH hpos 𝒯 h𝒯 hcomm hadj Z
    (full_eigen_commuting K Ω j n 𝒯 Z hZ) σ
end Formalism.DivisionValues
