-- Prove2me | solution 1 for Formalism.UG.P.satakeGL_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:54:07.913799+00:00
-- url     : https://prove2.me/submissions/8371c88b-40aa-4afd-bd58-4b9dbc0b6ff9

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Theorems.Thm_Formalism_UG_P_satakeN_lower
import Theorems.Thm_Formalism_UG_P_satakeGL_apply

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
variable {L : Type} [Field L] (O : Subring L) {n : ℕ}
variable {O}
variable (O)
namespace Formalism.UG.P
theorem _root_.solution {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) (c : satakePairs S → O) (a l : Fin n)
    (h : l < a) : ((satakeGL O hπ S c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a l = 0 := by
  rw [satakeGL_apply, Matrix.one_apply_ne h.ne', satakeN_lower O S c a l h, add_zero, zero_mul]
end Formalism.UG.P
