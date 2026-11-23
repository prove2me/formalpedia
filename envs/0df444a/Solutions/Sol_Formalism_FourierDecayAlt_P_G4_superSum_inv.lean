-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.superSum_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:32.217726+00:00
-- url     : https://prove2.me/submissions/fe8d1392-dcc6-42d1-a084-b45075053bf8

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upper_inv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upperUni_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_superSum_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_superSum_one

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
theorem _root_.solution {n : ℕ} {u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hu : IsUpperUni u) :
    superSum u⁻¹ + superSum u = 0 := by
  rw [← superSum_mul (upperUni_inv hu) hu, upper_inv_mul hu, superSum_one]
end Formalism.FourierDecayAlt.P.G4
