-- Prove2me | solution 1 for Formalism.NG.blockRhoCount
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:17:38.955397+00:00
-- url     : https://prove2.me/submissions/c72305cd-385a-4251-93d7-29111ff6c618

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockRhoCount
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Theorems.Thm_Formalism_NG_blockRhoAbs
import Theorems.Thm_Formalism_NG_kerCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatBlockRhoCount := by
  intro O _ _ _ G _ d _ ρM H _ _ Ψ δ hδ ι _ what₂ cols D F lenRow Q s ℓ e' j h0
  intro eO vδ N hrow hcol hQ hs Xw _ _ hX f hf
  exact blockRhoAbs O G d ρM H Ψ δ hδ ι what₂ cols D F lenRow Q s ℓ e' j h0 hrow hcol hQ hs
    (kerCount O (LinearMap.ker Ψ) ι cols ℓ δ e' j d Xw h0 hX f hf)
end Formalism.NG
