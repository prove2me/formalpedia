-- Prove2me | solution 1 for Formalism.UG.P.fSatake_unit_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:50:09.083006+00:00
-- url     : https://prove2.me/submissions/e4040183-e1a6-4d1a-9ef0-050a294a3b7a

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Theorems.Thm_Formalism_UG_P_fSatake_unit_diag_mat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    σ ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) *
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i.rev i.rev = 1 :=
  fSatake_unit_diag_mat hb b.2 i
end Formalism.UG.P
