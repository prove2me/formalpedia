-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.stab_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:13.195238+00:00
-- url     : https://prove2.me/submissions/bf71a089-5e26-41fb-a9b7-a8697be31d22

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_w_mul_w

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
theorem _root_.solution {d : ℕ} {l k k' : Matrix (Fin d) (Fin d) ℂ} (h1 : l * k = 1)
    (h2 : k * wMat d * k' = wMat d) : k' = wMat d * l * wMat d := by
  calc k' = (wMat d * wMat d) * k' := by rw [w_mul_w, Matrix.one_mul]
    _ = wMat d * (l * k) * wMat d * k' := by rw [h1, Matrix.mul_one]
    _ = wMat d * l * (k * wMat d * k') := by simp only [Matrix.mul_assoc]
    _ = wMat d * l * wMat d := by rw [h2]
end Formalism.FourierDecayAlt.P.G4
