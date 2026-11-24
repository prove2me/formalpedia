-- Prove2me | solution 1 for Formalism.L2.Th1.B.Map.baseChangeCompatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:01:41.988106+00:00
-- url     : https://prove2.me/submissions/dc21ccb2-87cd-47ed-aa01-f0a6f19d75cf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_BaseChangeCompatible
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_sigma
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_sgStar
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_sigma1
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_wOf
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_phO
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_phE
import Theorems.Thm_Formalism_L2_Th1_B_Map_map_cob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Map
open Formalism.InvariantFactorPaths.G7 (at1 cob)
variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')
namespace Formalism.L2.Th1.B.Map
theorem _root_.solution : BaseChange := by
  intro K K' _ _ _ _ j s2 e1 kap P w l F h0 h1 hF
  exact ⟨map_sigma j P, map_sgStar j s2 P, map_sigma1 j e1 kap w,
    map_wOf j e1 P, map_phO j s2 P h0 h1,
    map_phE j s2 e1 kap w h0, fun f => map_cob j hF f⟩
end Formalism.L2.Th1.B.Map
