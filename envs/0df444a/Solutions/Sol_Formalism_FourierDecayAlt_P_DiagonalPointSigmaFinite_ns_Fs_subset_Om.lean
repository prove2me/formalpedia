-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_Fs_subset_Om
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:03.078256+00:00
-- url     : https://prove2.me/submissions/68cc8035-5d2d-4e56-bcb6-d0dd6bc25203

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseEstimates

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
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
theorem _root_.solution (m : ℕ) (D' : ℂ) {R r r' d d' : ℝ} (hr : r' < r) (hd : d' < d) :
    ns_Fs m D' R r d ⊆ ns_Om m D' r' d' := by
  intro x hx
  exact ⟨fun k => hr.trans_le (hx.1 k).2, fun z hz => hd.trans_le (hx.2 z hz)⟩
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
