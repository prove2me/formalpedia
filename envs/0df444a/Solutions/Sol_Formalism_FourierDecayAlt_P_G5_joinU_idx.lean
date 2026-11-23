-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.joinU_idx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:05.326907+00:00
-- url     : https://prove2.me/submissions/519a12b0-c419-4abe-b12b-4bdccf508bba

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution {n : ℕ} (q : (UT n → ℂ) × (Fin n → ℂ)) (s : UT n ⊕ Fin n) :
    joinU q (idxEquiv n s) = Sum.elim q.1 q.2 s := by
  simp [joinU]
end Formalism.FourierDecayAlt.P.G5
