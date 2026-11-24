-- Prove2me | solution 1 for Formalism.NG.blockRhoFull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:25:21.768797+00:00
-- url     : https://prove2.me/submissions/11154dc6-f6fe-477b-a2b3-b757ef0de9c4

import Definitions.Def_Formalism_CharacterColumnKernels_StatementPsi
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CupKillAdm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull
import Theorems.Thm_Formalism_NG_colPsiKer
import Theorems.Thm_Formalism_NG_cobColumn
import Theorems.Thm_Formalism_NG_blockRhoColumn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : BlockRhoFull₂ := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j e' Kc k0
    ℓ sE tE hE hEE hEm hk0 hδ hτ hiso hloc
  exact blockRhoColumn O A T' G d r χ E e₁ δ δO ι ι' colIdx hinj D j e' Kc k0 ℓ hEm hk0
    (fun m => by rw [algebraMap_smul]; exact hδ m) hiso hloc (uRep O (M := d → KO O) r χ)
    (colPsi (O := O) (M := d → KO O) r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0)
    (colPsiKer O A T' G (d → KO O) r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0)
    (fun h v hv => cobColumn O A T' G (d → KO O) r χ E e₁ δ δO ι (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0 sE tE hE hEE hEm hδ hτ h v hv)
end Formalism.NG
