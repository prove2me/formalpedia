-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.lower_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:08.034079+00:00
-- url     : https://prove2.me/submissions/f7c947db-c80c-4565-bb60-f6977271b1ab

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_lowerUni_det

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
theorem _root_.solution {d : ℕ} {l : Matrix (Fin d) (Fin d) ℂ} (hl : IsLowerUni l) : l⁻¹ * l = 1 :=
  Matrix.nonsing_inv_mul l (by rw [lowerUni_det hl]; exact isUnit_one)
end Formalism.FourierDecayAlt.P.G4
