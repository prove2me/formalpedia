-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_idx_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:48.152229+00:00
-- url     : https://prove2.me/submissions/f89795c4-c7e9-474a-b95f-02ba752487b9

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {𝔽 : Type} [Field 𝔽]
namespace Formalism.UG.P
theorem _root_.solution (n j : ℕ) : Function.Injective (tjcosets_idx n j) := by
  intro a b h
  have h1 := congrArg Fin.val h
  simp only [tjcosets_idx] at h1
  exact Fin.ext (by omega)
end Formalism.UG.P
