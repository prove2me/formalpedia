-- Prove2me | solution 1 for Formalism.L2.DIV.nabDelEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:00.363349+00:00
-- url     : https://prove2.me/submissions/966354fd-9359-4350-ad2f-c0444b828b6f

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_transLat_gLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution : NabDelEquiv := by
  intro K _ _ ι _ n lam M g
  exact ⟨transLat_gLat lam _ M g, transLat_gLat lam _ M g⟩
end Formalism.L2.DIV
