-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.gr_block_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:25.381381+00:00
-- url     : https://prove2.me/submissions/73e5ca3c-d631-4dd4-b0e1-c8cabcf09370

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
theorem _root_.solution (β : ℂ) (n : ℕ) (τ : ℝ) (Φ : Mat (n + 1) → V) (t c : ℂ) (p : BlockCoord n) :
    blockIntegrand β n Φ t c p =
      blockIntegrand β n (cutPhi τ Φ) t c p + blockIntegrand β n (cutPhiC τ Φ) t c p := by
  unfold blockIntegrand cutPhi cutPhiC
  rw [← smul_add, ← add_smul]
  push_cast
  rw [add_sub_cancel, one_smul]
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
