-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.contOn_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:36:38.750792+00:00
-- url     : https://prove2.me/submissions/d8f9af5b-1727-4f40-9ba3-33abeb6e1f0f

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B3
theorem _root_.solution {h : ℝ × ℝ → ℝ} (hh : ContinuousOn h Quad) : ContinuousOn (fun τ => max (h τ) 0) Quad := by
  have := (continuous_id.max continuous_const : Continuous fun y : ℝ => max y 0).comp_continuousOn hh
  exact this
end Formalism.FourierDecayAlt.P.B3
