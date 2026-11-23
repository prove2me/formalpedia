-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_isClosed_Fs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:09.555967+00:00
-- url     : https://prove2.me/submissions/eb3b4a71-9de2-41f0-85f2-de453eb81f27

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
theorem _root_.solution (m : ℕ) (D' : ℂ) (R r d : ℝ) : IsClosed (ns_Fs m D' R r d) := by
  have : ns_Fs m D' R r d = (⋂ k, {x : Fin (m + 1) → ℂ | ‖x k‖ ≤ R} ∩ {x : Fin (m + 1) → ℂ | r ≤ ‖x k‖}) ∩
      (⋂ z ∈ rootSet (m + 2) D', {x : Fin (m + 1) → ℂ | d ≤ ‖x - fun _ => z‖}) := by
    ext x; simp [ns_Fs]
  rw [this]
  exact (isClosed_iInter fun k => (isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_le continuous_const (by fun_prop))).inter
    (isClosed_biInter fun z _ => isClosed_le continuous_const (by fun_prop))
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
