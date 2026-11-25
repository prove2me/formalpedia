-- Prove2me | solution 1 for Formalism.DV.gaussLocalizationIsDVR_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:22:16.396375+00:00
-- url     : https://prove2.me/submissions/c554fa0c-5dd3-4c79-bb77-5586859be357

import Definitions.Def_Formalism_GaussIdealIdentity_StatementLA
import Definitions.Def_Formalism_GaussIdealIdentity_GaussIdealPrimality_GaussLocalizationLengthHolds
import Theorems.Thm_Formalism_DV_GaussP_gaussIdeal_isPrime
import Theorems.Thm_Formalism_DV_GaussP_maximalIdeal_eq
import Theorems.Thm_Formalism_DV_GaussP_isDVR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial IsLocalRing
noncomputable section
open Formalism.DV
namespace Formalism.DV
theorem _root_.solution : GaussDVR := by
  intro σ O _ _ _ _
  refine ⟨GaussP.gaussIdeal_isPrime σ O, ?_⟩
  intro _
  exact ⟨GaussP.isDVR σ O, GaussP.maximalIdeal_eq σ O⟩
end Formalism.DV
