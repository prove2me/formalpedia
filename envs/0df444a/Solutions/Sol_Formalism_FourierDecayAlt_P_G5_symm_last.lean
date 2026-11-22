-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.symm_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:46.262136+00:00
-- url     : https://prove2.me/submissions/03701d42-ed83-4787-9b8c-0e9229140404

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
theorem _root_.solution (n : ℕ) : finSumFinEquiv.symm (Fin.last n : Fin (n + 1)) = Sum.inr (0 : Fin 1) :=
  finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)
end Formalism.FourierDecayAlt.P.G5
