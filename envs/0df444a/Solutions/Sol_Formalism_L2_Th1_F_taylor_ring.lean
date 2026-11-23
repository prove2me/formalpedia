-- Prove2me | solution 1 for Formalism.L2.Th1.F.taylor_ring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:39.170094+00:00
-- url     : https://prove2.me/submissions/0908a34b-d7b7-4719-92ca-8f4001b1fd1c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_add
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_mul
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_const
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_id
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : TaylorRing :=
  ⟨fun _ _ hf hg => ⟨Taylor.taylor0_add hf hg, Taylor.taylor0_mul hf hg⟩, Taylor.taylor0_const,
    Taylor.taylor0_id, fun _ _ h => Taylor.taylor0_congr h⟩
end Formalism.L2.Th1.F
