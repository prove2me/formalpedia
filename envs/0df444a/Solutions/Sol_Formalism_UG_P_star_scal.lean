-- Prove2me | solution 1 for Formalism.UG.P.star_scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:48.203482+00:00
-- url     : https://prove2.me/submissions/72d32fff-b2f8-4224-a22e-1f37200b6af8

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Matrix
namespace Formalism.UG.P
theorem _root_.solution {n : Type} (ev : n → ℝ) : star (scal ev) = scal ev := by
  funext i
  simp only [Pi.star_apply, scal]
  exact Complex.conj_ofReal _
end Formalism.UG.P
