-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.fst_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:01:59.334845+00:00
-- url     : https://prove2.me/submissions/371c3c8b-307d-4a4d-869d-16d41ef9400e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge
noncomputable section
variable (P : M.Par)
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge
theorem _root_.solution (x y : (MA.DQ P).Pr) : (x + y).1 = x.1 + y.1 := rfl
end Formalism.FourierDecayAlt.P.CutMP.Gauge
