-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.revIn_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:18.982488+00:00
-- url     : https://prove2.me/submissions/1654386f-b3d7-43fd-b370-398edece13d0

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
theorem _root_.solution (s : List ℕ) : ∀ j, j < s.sum → revIn s j < s.sum := by
  induction s with
  | nil => intro j h; simp at h
  | cons c s ih =>
    intro j h
    simp only [List.sum_cons] at h ⊢
    simp only [revIn]
    split_ifs with h1
    · omega
    · have := ih (j - c) (by omega); omega
end Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
