-- Prove2me | solution 1 for Formalism.UG.dualWeylRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:16:00.587944+00:00
-- url     : https://prove2.me/submissions/44398ce2-9781-4ffd-9a20-3d74683c0ff2

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_DualWeylModuleStable
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_SatakeDualWeyl_DualWeylRepApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.UG
namespace Formalism.UG
theorem _root_.solution (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (g : GL (Fin r) R)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R r n ν) :
    ((dualWeylRep R r n ν g f : Formalism.GradedWeylDivisibility.dualWeyl R r n ν) : MvPolynomial (Fin r × Fin n) R) =
      dwAct R r n g f := rfl
end Formalism.UG
