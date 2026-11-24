-- Prove2me | solution 1 for Formalism.NG.kerHomRect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:42:11.045483+00:00
-- url     : https://prove2.me/submissions/0e12f7da-b45e-4df1-b7ca-7eca3e9362da

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenRelMapApply
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
import Theorems.Thm_Formalism_NG_genfin_ker_map_uncurry

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
theorem _root_.solution : StatKerHomRect := by
  intro R O _ _ _ _ m g d _ _ _ _ _ ρ _ P
  rw [(homEquiv (O := O) (M := LatQ O d ρ) P).length_eq]
  exact ((LinearEquiv.ofSubmodules (uncurryEquiv ρ) _ _ (genfin_ker_map_uncurry ρ P)).length_eq).symm
end Formalism.NG
