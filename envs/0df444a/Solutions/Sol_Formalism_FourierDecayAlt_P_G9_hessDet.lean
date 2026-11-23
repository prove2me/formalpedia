-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.hessDet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:10.336657+00:00
-- url     : https://prove2.me/submissions/7ff09424-8389-4120-9d36-02d027651127

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution : HessDet := by
  intro m z
  rw [Matrix.det_smul]
  have h : (Matrix.of fun _ _ => (1:ℂ) : Matrix (Fin (m+1)) (Fin (m+1)) ℂ)
      = Matrix.replicateCol Unit (fun _ : Fin (m+1) => (1:ℂ)) * Matrix.replicateRow Unit (fun _ : Fin (m+1) => (1:ℂ)) := by
    ext i j; simp [Matrix.mul_apply]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct]
  ring
end Formalism.FourierDecayAlt.P.G9
