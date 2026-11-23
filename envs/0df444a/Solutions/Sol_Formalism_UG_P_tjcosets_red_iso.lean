-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_red_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:17.020019+00:00
-- url     : https://prove2.me/submissions/53adbb5c-8672-4149-97d3-3e0a9a24ac72

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
namespace Formalism.UG.P
theorem _root_.solution (n : ℕ) (g : GL (Fin n) O) :
    tjcosets_red O n (tjcosets_iso n O g) = bc (IsLocalRing.residue O) g := by
  show bc _ ((tjcosets_iso n O).symm (tjcosets_iso n O g)) = _
  rw [MulEquiv.symm_apply_apply]
end Formalism.UG.P
