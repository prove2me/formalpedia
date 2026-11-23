-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Markov.th_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:25.374261+00:00
-- url     : https://prove2.me/submissions/d0116bbb-e0f5-4420-8576-bbe4fa637337

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset
namespace Formalism.FourierDecayAlt.P.Markov
theorem _root_.solution (n k : ℕ) (hn : n ≠ 0) : 0 < th n k := by
  have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold th; positivity
end Formalism.FourierDecayAlt.P.Markov
