-- Prove2me | solution 1 for Formalism.L2.NT.finrank_eq_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:58:32.877095+00:00
-- url     : https://prove2.me/submissions/9d53d3c1-bf3c-4abf-8221-222ceb886fa5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host
namespace Formalism.L2.NT
theorem _root_.solution {A B : Type} [Field A] [Field B] [CharZero A] [CharZero B] (e : A ≃+* B) :
    Module.finrank ℚ A = Module.finrank ℚ B :=
  LinearEquiv.finrank_eq e.toRatAlgEquiv.toLinearEquiv
end Formalism.L2.NT
