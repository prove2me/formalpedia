-- Prove2me | solution 1 for Formalism.REAL.thetaFil_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:57:41.647403+00:00
-- url     : https://prove2.me/submissions/623187e0-f0f4-48e2-b852-1a26405c3b99

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_theta_noncompact_mem_pfil
import Theorems.Thm_Formalism_REAL_pfil_succ_le_theta_image_sup
import Theorems.Thm_Formalism_REAL_symmetrization_perm_sub_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (hp : PfilFacts) : ThetaFil := by
  intro V _ _ n ε E u hE
  exact ⟨fun j F hF => theta_noncompact_mem_pfil ε E u j F hF, fun j => pfil_succ_le_theta_image_sup ε E u j,
    fun j F hF σ => symmetrization_perm_sub_mem ε E u hE j F hF σ⟩
end Formalism.REAL
