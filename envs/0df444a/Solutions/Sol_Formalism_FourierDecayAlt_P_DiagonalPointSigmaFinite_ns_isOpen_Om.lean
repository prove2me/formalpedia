-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.ns_isOpen_Om
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:09.579051+00:00
-- url     : https://prove2.me/submissions/46eeea1f-ec9c-4404-9539-4e6cd0a220a5

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
theorem _root_.solution (m : ℕ) (D' : ℂ) (r d : ℝ) : IsOpen (ns_Om m D' r d) := by
  have : ns_Om m D' r d = (⋂ k, {x : Fin (m + 1) → ℂ | r < ‖x k‖}) ∩
      (⋂ z ∈ rootSet (m + 2) D', {x : Fin (m + 1) → ℂ | d < ‖x - fun _ => z‖}) := by
    ext x; simp [ns_Om]
  rw [this]
  exact (isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (by fun_prop)).inter
    (isOpen_biInter_finset fun z _ => isOpen_lt continuous_const (by fun_prop))
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
