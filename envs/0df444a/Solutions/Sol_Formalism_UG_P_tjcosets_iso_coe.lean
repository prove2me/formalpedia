-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_iso_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:39:48.768384+00:00
-- url     : https://prove2.me/submissions/dc8fb04c-3876-494e-a7ba-b381d39f3fb1

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc

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
open Formalism.UG
variable {L : Type} [Field L]
namespace Formalism.UG.P
theorem _root_.solution (n : ℕ) (O : Subring L) (g : GL (Fin n) O) :
    ((tjcosets_iso n O g : GLint (Fin n) O) : GL (Fin n) L) = bc O.subtype g := by
  exact MonoidHom.ofInjective_apply (tjcosets_bc_injective n O)
end Formalism.UG.P
