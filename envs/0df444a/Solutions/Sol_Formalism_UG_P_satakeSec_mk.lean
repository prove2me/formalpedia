-- Prove2me | solution 1 for Formalism.UG.P.satakeSec_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:42.228183+00:00
-- url     : https://prove2.me/submissions/e4406b94-3db6-4e7b-a6d9-99916c7240fc

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat

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
theorem _root_.solution (π : O) (r : satakeRes O π) : Ideal.Quotient.mk _ (satakeSec O π r) = r :=
  Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {π})) r
end Formalism.UG.P
