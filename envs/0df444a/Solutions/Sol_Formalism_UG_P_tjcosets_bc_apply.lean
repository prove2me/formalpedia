-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_bc_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:01:21.537475+00:00
-- url     : https://prove2.me/submissions/0784a79f-fbfa-4668-adc9-e6251fa6e946

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
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (n : ℕ)
    (g : GL (Fin n) A) (a b : Fin n) :
    ((bc (n := Fin n) φ g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) a b = φ ((g : Matrix (Fin n) (Fin n) A) a b) := by
  rfl
end Formalism.UG.P
