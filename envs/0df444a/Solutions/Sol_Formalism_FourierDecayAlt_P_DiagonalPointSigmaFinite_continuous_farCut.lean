-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.continuous_farCut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:17:18.386789+00:00
-- url     : https://prove2.me/submissions/4f872b43-13eb-42fa-9524-c12c7fefdc6d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiagonalPointSigmaFinite_continuous_critCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
theorem _root_.solution (m : ℕ) (δ : ℝ) (D : ℂ) : Continuous (farCut m δ D) := by
  unfold farCut
  exact continuous_const.sub (continuous_finsetSum _ fun z _ => continuous_critCut δ z)
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
