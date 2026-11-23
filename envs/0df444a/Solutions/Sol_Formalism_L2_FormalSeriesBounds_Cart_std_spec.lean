-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Cart.std_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:39.543796+00:00
-- url     : https://prove2.me/submissions/fb75f8e5-8b35-4413-bc6b-215cab2ae8b0

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Finset
noncomputable section
variable {C : Type*} [Field C] {V : VF C} {d : ℕ} {I J : Type*}
open Formalism.L2.FormalSeriesBounds.Cart
variable (X : Cart V d I J)
variable [DecidableEq I]
namespace Formalism.L2.FormalSeriesBounds.Cart
theorem _root_.solution (b : I) : X.IsCurve (X.ty (Sum.inl b)) (Pi.single b 1) (X.std b) :=
  Classical.choose_spec (X.exists_std b)
end Formalism.L2.FormalSeriesBounds.Cart
