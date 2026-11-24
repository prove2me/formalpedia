-- Prove2me | solution 1 for Formalism.mxS_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:46:36.133187+00:00
-- url     : https://prove2.me/submissions/da7dca7c-5c95-47c7-ba50-54d3cf189ee0

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution (n : ℕ) (x : ℝ) : 0 ≤ mxS n x := by
  show 0 ≤ max (x / n - 1) 0
  exact le_max_right _ _
end Formalism
