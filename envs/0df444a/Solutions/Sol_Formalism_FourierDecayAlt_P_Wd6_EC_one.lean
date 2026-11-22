-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.EC.one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:48:42.775611+00:00
-- url     : https://prove2.me/submissions/eb745f93-b671-4a7e-93a2-2aab0527d5fb

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {B : Type} [Ring B]
namespace Formalism.FourierDecayAlt.P.Wd6
namespace EC
theorem _root_.solution (z : B) : EC z (1 : M2 B) := by
  intro i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]
end EC
end Formalism.FourierDecayAlt.P.Wd6
