-- Prove2me | solution 1 for Formalism.UG.P.bc_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:13.075206+00:00
-- url     : https://prove2.me/submissions/760bbd05-b54a-47c2-97c7-a8dcc3fb4aba

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (φ : A →+* B) (g : GL n A) : ((bc φ g : GL n B) : Matrix n n B) = (g : Matrix n n A).map φ :=
  rfl
end Formalism.UG.P
