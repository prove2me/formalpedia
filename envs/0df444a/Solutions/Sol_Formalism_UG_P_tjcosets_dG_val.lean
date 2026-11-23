-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_dG_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:16.7175+00:00
-- url     : https://prove2.me/submissions/2448ff8b-4244-4117-b84b-47245c690030

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
variable (O : Subring L) [IsLocalRing O]
variable {O}
namespace Formalism.UG.P
theorem _root_.solution (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0) :
    ((tjcosets_dG n j ϖ hϖ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = diagJ n ϖ j := rfl
end Formalism.UG.P
