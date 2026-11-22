-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.psi_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:40.288684+00:00
-- url     : https://prove2.me/submissions/a6635bba-7391-4f8f-96e4-2ac528455c6a

import Definitions.Def_Formalism_LogSumExpBounds_StatementZ
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LatSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution (n : ℤ) : 0 ≤ psi n := by
  unfold psi; positivity
end Formalism.NuclearRankWeightBounds.P
