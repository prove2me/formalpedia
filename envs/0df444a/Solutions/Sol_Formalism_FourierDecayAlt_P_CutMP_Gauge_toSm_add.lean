-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:09:56.724106+00:00
-- url     : https://prove2.me/submissions/2ba7b321-a8ca-42b8-b4c3-2473cbecc400

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_toSm_of_mem

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
theorem _root_.solution {u v : MA.Qp P.r P.TT → ℂ} (hu : u ∈ MA.smSub P.r P.TT) (hv : v ∈ MA.smSub P.r P.TT) :
    MA.toSm P (u + v) = MA.toSm P u + MA.toSm P v := by
  rw [toSm_of_mem P hu, toSm_of_mem P hv, toSm_of_mem P (add_mem hu hv)]
  rfl
end Formalism.FourierDecayAlt.P.CutMP.Gauge
