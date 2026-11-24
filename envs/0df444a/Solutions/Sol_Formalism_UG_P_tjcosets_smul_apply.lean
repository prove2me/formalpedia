-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_smul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:52.073608+00:00
-- url     : https://prove2.me/submissions/f610be6e-bf86-49a6-b2d9-31795692b2e7

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
theorem _root_.solution {m n : ℕ} (g : GL (Fin n) 𝔽) (w : TjcosetsFr m n 𝔽) (i : Fin m) :
    (g • w) i = (g : Matrix (Fin n) (Fin n) 𝔽) *ᵥ w i := rfl
end Formalism.UG.P
