-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.jdh_actA_zeroR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:02:47.41033+00:00
-- url     : https://prove2.me/submissions/2ab4545f-34ae-446b-bd8b-aa2fde86bbf4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
open NumberField
noncomputable section
variable (P : M.Par)
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution (a : MA.A P (MA.DQ P)) : MA.actA P a 0 = 0 := by
  funext π
  show ∑ π', (a π π').1 0 = 0
  exact Finset.sum_eq_zero fun π' _ => map_zero _
end Formalism.FourierDecayAlt.P.CutMP
