-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.actA_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:43:39.02829+00:00
-- url     : https://prove2.me/submissions/ace48302-0f63-4cfa-95cc-121b5323e6cd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_fst_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_op_zero_apply

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
theorem _root_.solution (f : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 0 f = 0 := by
  funext π
  simp only [MA.actA, Matrix.zero_apply, fst_zero, Pi.zero_apply]
  exact Finset.sum_eq_zero fun π' _ => op_zero_apply P (f π')
end Formalism.FourierDecayAlt.P.CutMP.Gauge
