-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.actA_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:43:35.82166+00:00
-- url     : https://prove2.me/submissions/268f4596-705f-46b0-802b-f8f4d4b6ae2d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_fst_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_op_add_apply

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
theorem _root_.solution (x y : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (x + y) f = MA.actA P x f + MA.actA P y f := by
  funext π
  simp only [MA.actA, Matrix.add_apply, fst_add, Pi.add_apply]
  exact (Finset.sum_congr rfl fun π' _ => op_add_apply P _ _ (f π')).trans Finset.sum_add_distrib
end Formalism.FourierDecayAlt.P.CutMP.Gauge
