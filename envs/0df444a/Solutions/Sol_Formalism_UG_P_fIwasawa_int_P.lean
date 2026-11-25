-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_int_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:23:46.054506+00:00
-- url     : https://prove2.me/submissions/5638573a-2a59-4307-b5f3-c31ffdfa9fa0

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
theorem _root_.solution (π : Equiv.Perm (Fin n)) : fIwasawaInt (fIwasawaP (L := L) π) := by
  intro i j
  simp only [fIwasawaP, Matrix.of_apply]
  split_ifs <;> simp
end Formalism.UG.P
