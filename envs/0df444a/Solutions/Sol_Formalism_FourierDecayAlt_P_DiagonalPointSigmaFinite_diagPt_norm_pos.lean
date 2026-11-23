-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.diagPt_norm_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:25.228252+00:00
-- url     : https://prove2.me/submissions/cfdeaa14-ba52-442e-a57f-36a387bd6278

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
theorem _root_.solution (s : ℕ) (a : ℂ) : 0 < ‖diagPt s a‖ := by
  rw [norm_pos_iff]
  intro h
  have h1 : diagPt s a (Fin.last (s + 1)) (Fin.last (s + 1)) = 0 := by rw [h]; rfl
  have h2 : diagPt s a (Fin.last (s + 1)) (Fin.last (s + 1)) = 1 := by
    unfold diagPt
    rw [Matrix.diagonal_apply_eq, if_neg (Fin.last_pos).ne']
  rw [h2] at h1
  exact one_ne_zero h1
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
