-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_int_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:13.363565+00:00
-- url     : https://prove2.me/submissions/c4ee4af9-11c7-4cd3-b87a-e77b54623356

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
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) L) (hA : fIwasawaInt A) (hB : fIwasawaInt B) :
    fIwasawaInt (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun k _ => by rw [map_mul]; exact mul_le_one' (hA i k) (hB k j)
end Formalism.UG.P
