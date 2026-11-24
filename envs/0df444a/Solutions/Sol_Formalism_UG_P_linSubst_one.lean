-- Prove2me | solution 1 for Formalism.UG.P.linSubst_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:58.010809+00:00
-- url     : https://prove2.me/submissions/b527c1f7-41c9-47dd-b072-07e794cc1daf

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Matrix MvPolynomial
namespace Formalism.UG.P
theorem _root_.solution (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Formalism.UG.linSubst O n 1 = AlgHom.id O _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [Formalism.UG.linSubst, Matrix.one_apply]
end Formalism.UG.P
