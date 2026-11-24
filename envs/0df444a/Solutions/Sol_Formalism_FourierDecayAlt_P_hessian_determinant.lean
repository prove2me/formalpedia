-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.hessian_determinant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:57.193533+00:00
-- url     : https://prove2.me/submissions/e8e6928b-9b3e-4750-bd1b-80d1f53e92a6

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.HessDet := by
  intro m z
  rw [Matrix.det_smul, Fintype.card_fin]
  have hJ : (Matrix.of fun _ _ => (1 : ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      Matrix.replicateCol Unit (fun _ => (1 : ℂ)) * Matrix.replicateRow Unit (fun _ => (1 : ℂ)) := by
    ext i j; simp [Matrix.mul_apply]
  rw [hJ, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct]
  ring
end Formalism.FourierDecayAlt.P
