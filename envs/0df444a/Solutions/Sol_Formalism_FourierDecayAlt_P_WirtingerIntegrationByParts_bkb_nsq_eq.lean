-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_nsq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:15.182206+00:00
-- url     : https://prove2.me/submissions/849e3e79-b3d0-44af-a6df-87b6ef477dcd

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution (z : ℂ) : Complex.normSq z = Complex.reCLM ((starRingEnd ℂ) z • z) := by
  rw [smul_eq_mul, ← Complex.normSq_eq_conj_mul_self]; simp
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
