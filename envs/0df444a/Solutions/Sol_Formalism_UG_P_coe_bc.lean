-- Prove2me | solution 1 for Formalism.UG.P.coe_bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:14.201479+00:00
-- url     : https://prove2.me/submissions/48b27980-bf94-46a9-8742-c87245401eea

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Matrix
variable {A R : Type} [CommRing A] [CommRing R] [Algebra R A] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (φ : R →+* A) (u : GL n R) :
    ((bc (n := n) φ u : GL n A) : Matrix n n A) = (u : Matrix n n R).map φ := by
  rfl
end Formalism.UG.P
