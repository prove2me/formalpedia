-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_int_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:03.069451+00:00
-- url     : https://prove2.me/submissions/8f3991e6-58fc-46a3-ac7c-9a1d94b8f324

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution : fIwasawaInt (1 : Matrix (Fin n) (Fin n) L) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp
end Formalism.UG.P
