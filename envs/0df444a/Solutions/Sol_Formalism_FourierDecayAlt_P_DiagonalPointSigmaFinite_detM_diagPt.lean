-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite.detM_diagPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:24.877797+00:00
-- url     : https://prove2.me/submissions/7a6230d1-e042-4cac-b573-da6676ca72ae

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
theorem _root_.solution (s : ℕ) (a : ℂ) : detM (diagPt s a) = a := by
  unfold detM diagPt
  have : (Matrix.of (Matrix.diagonal (fun i : Fin (s + 2) => if i = 0 then a else 1)) :
      Matrix (Fin (s + 2)) (Fin (s + 2)) ℂ) = Matrix.diagonal (fun i : Fin (s + 2) => if i = 0 then a else 1) := rfl
  rw [this, Matrix.det_diagonal, Finset.prod_ite_eq']
  simp
end Formalism.FourierDecayAlt.P.DiagonalPointSigmaFinite
