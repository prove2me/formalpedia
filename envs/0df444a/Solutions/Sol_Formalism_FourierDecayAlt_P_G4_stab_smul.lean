-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.stab_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:47:06.591041+00:00
-- url     : https://prove2.me/submissions/c951177f-2cdc-4404-b81e-6812aa5ceb8d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {d : ℕ} {z : ℂ} (hz : z ≠ 0) (l u : Matrix (Fin d) (Fin d) ℂ) :
    l * (z • wMat d) * u = z • wMat d ↔ l * wMat d * u = wMat d := by
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact (smul_right_injective _ hz).eq_iff
end Formalism.FourierDecayAlt.P.G4
