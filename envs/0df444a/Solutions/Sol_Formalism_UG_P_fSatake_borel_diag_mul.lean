-- Prove2me | solution 1 for Formalism.UG.P.fSatake_borel_diag_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:51:29.358799+00:00
-- url     : https://prove2.me/submissions/44771fd6-4bed-47f8-8f9a-ec2203c2c122

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Theorems.Thm_Formalism_UG_P_fSatake_borel_iff
import Theorems.Thm_Formalism_UG_P_fSatake_diag_mul

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
theorem _root_.solution {b b' : GU σ n} (hb : IsBorelU b) (hb' : IsBorelU b') (i : Fin n) :
    (((b * b' : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((b' : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
  have := fSatake_diag_mul ((fSatake_borel_iff b).1 hb) ((fSatake_borel_iff b').1 hb') i
  simpa only [Subgroup.coe_mul, Units.val_mul] using this
end Formalism.UG.P
