-- Prove2me | solution 1 for Formalism.UG.P.sigex_cT_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:39:49.705732+00:00
-- url     : https://prove2.me/submissions/cd68fe87-67a7-4896-afcd-9cd8fac1e3e1

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
theorem _root_.solution {m p : Type} (M : Matrix m p ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  first
    | rfl
    | (ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply])
end Formalism.UG.P
