-- Prove2me | solution 1 for Formalism.UG.P.fSatake_borel_diag_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:58.572916+00:00
-- url     : https://prove2.me/submissions/a4c04dd4-cee6-4961-9f97-fdef40f95222

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Theorems.Thm_Formalism_UG_P_fSatake_borel_inv
import Theorems.Thm_Formalism_UG_P_fSatake_borel_diag_mul

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
    (((b⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
  rw [← fSatake_borel_diag_mul (fSatake_borel_inv hb) hb i]
  simp
end Formalism.UG.P
