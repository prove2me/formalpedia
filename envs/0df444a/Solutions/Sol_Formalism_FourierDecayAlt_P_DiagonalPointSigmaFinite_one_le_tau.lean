-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.one_le_tau
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:44.940723+00:00
-- url     : https://prove2.me/submissions/1d50a21a-fb8a-4314-a3a4-8586f8ecae12

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
theorem _root_.solution {t : ℂ} {ε : ℝ} (ht : t ≠ 0) (ht1 : ‖t‖ ≤ 1) (hε : 0 ≤ ε) : 1 ≤ ‖t‖ ^ (-ε) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos (norm_pos_iff.mpr ht) ht1 (by linarith)
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
