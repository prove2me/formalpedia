-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.gr_osc_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:25.496796+00:00
-- url     : https://prove2.me/submissions/c0f84b2e-bfa3-4f92-9a71-a5f61687effc

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
theorem _root_.solution (β : ℂ) (m : ℕ) (δ ε : ℝ) (Φ : Mat (m + 1 + 1) → V) (D t : ℂ) (p : XY m) :
    oscIn β m ε Φ D t p = ((farCut m δ D p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p +
      ∑ z ∈ rootSet (m + 2) ((-1) ^ (m + 3) * D), ((critCut δ z p.1 : ℝ) : ℂ) • oscIn β m ε Φ D t p := by
  rw [← Finset.sum_smul, ← add_smul]
  unfold farCut
  push_cast
  rw [sub_add_cancel, one_smul]
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
