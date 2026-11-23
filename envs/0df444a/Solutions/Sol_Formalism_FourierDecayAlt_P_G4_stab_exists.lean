-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.stab_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:44.101808+00:00
-- url     : https://prove2.me/submissions/e5c27c0c-eb72-4e2e-b19e-023e627262dc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_lower_inv_mul
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
theorem _root_.solution {d : ℕ} {l : Matrix (Fin d) (Fin d) ℂ} (hl : IsLowerUni l) :
    l⁻¹ * wMat d * (wMat d * l * wMat d) = wMat d := by
  calc l⁻¹ * wMat d * (wMat d * l * wMat d) = l⁻¹ * ((wMat d * wMat d) * l) * wMat d := by
          simp only [Matrix.mul_assoc]
    _ = wMat d := by rw [w_mul_w, Matrix.one_mul, lower_inv_mul hl, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.G4
