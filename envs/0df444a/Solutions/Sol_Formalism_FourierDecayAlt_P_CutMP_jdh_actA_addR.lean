-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.jdh_actA_addR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:01:27.236401+00:00
-- url     : https://prove2.me/submissions/b169b84b-83af-4dbc-bf9b-df2e5da59442

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
theorem _root_.solution (a : MA.A P (MA.DQ P)) (x y : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P a (x + y) = MA.actA P a x + MA.actA P a y := by
  funext π
  show ∑ π', (a π π').1 (x π' + y π') = ∑ π', (a π π').1 (x π') + ∑ π', (a π π').1 (y π')
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => map_add _ _ _
end Formalism.FourierDecayAlt.P.CutMP
