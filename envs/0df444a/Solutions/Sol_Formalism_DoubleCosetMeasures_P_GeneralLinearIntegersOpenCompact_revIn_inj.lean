-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.revIn_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:35.340521+00:00
-- url     : https://prove2.me/submissions/ef3ef800-49c6-42bf-8c14-432c65c6d87b

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
variable {K : Type} [CommRing K]
namespace Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
theorem _root_.solution (s : List ℕ) : Function.Injective (revIn s) := by
  induction s with
  | nil => intro j k h; simpa [revIn] using h
  | cons c s ih =>
    intro j k h
    simp only [revIn] at h
    by_cases h1 : j < c <;> by_cases h2 : k < c <;> simp only [h1, h2, if_true, if_false] at h
    · omega
    · omega
    · omega
    · have := ih (Nat.add_left_cancel h); omega
end Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
