-- Prove2me | solution 1 for Formalism.NG.globalColumn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:03:31.285393+00:00
-- url     : https://prove2.me/submissions/15559b72-8bec-4532-8914-94cccf9ef1a9

import Definitions.Def_Formalism_CharacterColumnKernels_StatementGC
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalModuleOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CupKillAdm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalColumn
import Theorems.Thm_Formalism_NG_columnJ
import Theorems.Thm_Formalism_NG_globalModule


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
theorem _root_.solution : StatGlobalColumn := by
  intro O _ _ _ X X' T T' Z p q b hspan hinj d _ _ R' _ hdet Tc _ _ _ _ G _ r χ E e₁ δ ι _ _ D j
    Kc k0 hE he₁ hpt g₀ n hn π' ρπ hρπ α _ _ bl hbl ρk hρk hblk _ hcard
  refine globalModule O X X' T T' Z p q b hspan hinj d R' hdet
    (ColNNJ r χ E e₁ δ D j Kc k0) g₀ n hn ?_ π' ρπ hρπ α bl hbl ρk hρk hblk hcard
  intro x' hx'
  obtain ⟨δx, hδx, hδ, hEr, he₁r, hfix, hL⟩ := hpt x' hx'
  exact columnJ R' Tc (FractionRing O) (EvalSp O d R' x') G r χ E e₁ δ ι D j Kc k0 hE he₁
    δx hδx hδ hEr he₁r hfix hL
end Formalism.NG
