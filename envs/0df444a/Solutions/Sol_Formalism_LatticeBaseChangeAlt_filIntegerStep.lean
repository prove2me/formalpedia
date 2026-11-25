-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.filIntegerStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:18.697314+00:00
-- url     : https://prove2.me/submissions/bad65174-2965-48c6-b012-4e93f719f643

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FilIntegerStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : FilIntegerStep := by
  intro νF νE T c φ μ h1 h2 h3
  have hT : (0 : ℝ) ≤ T := by positivity
  have : ((T : ℤ) * νE : ℤ) < νF := by
    have : ((T : ℝ) * νE) < νF := by nlinarith
    exact_mod_cast this
  omega
end Formalism.LatticeBaseChangeAlt
