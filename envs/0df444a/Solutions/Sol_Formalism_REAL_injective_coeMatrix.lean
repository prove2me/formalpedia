-- Prove2me | solution 1 for Formalism.REAL.injective_coeMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:05.544328+00:00
-- url     : https://prove2.me/submissions/a7aeea69-7368-46a3-83c3-90eb2b47ebc3

import Definitions.Def_Formalism_RealPlaceAnalysis_UJLocCompact
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsInducingCoeMatrix
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) : Function.Injective (coeMatrixAlt ε) := by
  intro a b h
  exact Subtype.ext (Units.ext h)
end Formalism.REAL
