-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.ann_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:36:44.57827+00:00
-- url     : https://prove2.me/submissions/a70653d5-279b-476e-8f3a-722a10961bd7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution (P : M.Par) (hTT : 0 < P.TT) : ((Real.sqrt P.TT + 1 : ℝ) : ℂ) ∈ Ann P := by
  show P.TT < Complex.normSq (((Real.sqrt P.TT + 1 : ℝ)) : ℂ)
  rw [Complex.normSq_ofReal]
  have h1 := Real.sq_sqrt hTT.le
  have h2 := Real.sqrt_nonneg P.TT
  nlinarith
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
