-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.stabilizer_long_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:16.496796+00:00
-- url     : https://prove2.me/submissions/e686a49c-95f6-4e70-937d-e0594abf98c0

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_superSum_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_subSum_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_smul

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open G4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.StabLong := by
  intro n z hz l u _ hu
  have h1 : l * ptLong (n + 1) z * u = ptLong (n + 1) z ↔ l = wMat (n + 1) * u⁻¹ * wMat (n + 1) := by
    unfold ptLong
    rw [stab_smul hz, stab_core hu]
  refine ⟨h1, fun h => ?_⟩
  rw [h1.1 h, subSum_conj, superSum_inv hu]
end Formalism.FourierDecayAlt.P
