-- Prove2me | solution 1 for Formalism.UG.P.satakeGL_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:47.27395+00:00
-- url     : https://prove2.me/submissions/e4e2d7ab-77c0-41e5-abc8-7cb1b0ce9b40

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Theorems.Thm_Formalism_UG_P_satakeN_diag
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
theorem _root_.solution {π : L} (hπ : π ≠ 0) (S : Finset (Fin n)) (c : satakePairs S → O) (a : Fin n) :
    ((satakeGL O hπ S c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a = if a ∈ S then π else 1 := by
  rw [satakeGL_apply, Matrix.one_apply_eq, satakeN_diag, add_zero, one_mul]
end Formalism.UG.P
