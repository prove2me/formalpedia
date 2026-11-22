-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.continuous_coordU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:47:49.22986+00:00
-- url     : https://prove2.me/submissions/1c914e4b-771a-44d8-b685-45928c6243b3

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
theorem _root_.solution (d : ℕ) : Continuous (coordU : Matrix (Fin d) (Fin d) ℂ → UT d → ℂ) :=
  continuous_pi fun p => continuous_id.matrix_elem p.1.1 p.1.2
end Formalism.FourierDecayAlt.P.G5
