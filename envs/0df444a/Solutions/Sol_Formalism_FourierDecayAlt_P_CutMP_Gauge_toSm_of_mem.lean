-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:02:03.655358+00:00
-- url     : https://prove2.me/submissions/ea753d34-22b2-40af-bc02-acb2f69901d5

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
theorem _root_.solution {u : MA.Qp P.r P.TT → ℂ} (h : u ∈ MA.smSub P.r P.TT) : MA.toSm P u = ⟨u, h⟩ := by
  simp [MA.toSm, h]
end Formalism.FourierDecayAlt.P.CutMP.Gauge
