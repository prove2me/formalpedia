-- Prove2me | solution 1 for Formalism.ResultantValuation.ParabolicCounting.finrank_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:47:46.382372+00:00
-- url     : https://prove2.me/submissions/a054df8a-be8b-4f17-ada2-a217eadbf9d2

import Definitions.Def_Formalism_ResultantValuation_SubspaceCount
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Parabolic
import Theorems.Thm_Formalism_ResultantValuation_ParabolicCounting_smul_def
import Theorems.Thm_Formalism_ResultantValuation_ParabolicCounting_lequiv_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ResultantValuation
open Module
open Formalism.ResultantValuation.ParabolicCounting
variable (F : Type) [Field F] (r t : ℕ)
attribute [local instance] act
namespace Formalism.ResultantValuation.ParabolicCounting
theorem _root_.solution (g : GL (Fin (r + t)) F) (W : Submodule F (Fin (r + t) → F)) :
    finrank F (g • W : Submodule F (Fin (r + t) → F)) = finrank F W := by
  rw [smul_def, ← lequiv_coe, LinearEquiv.finrank_map_eq]
end Formalism.ResultantValuation.ParabolicCounting
