-- Prove2me | solution 1 for Formalism.L2.DIV.delLeNab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:41:37.0688+00:00
-- url     : https://prove2.me/submissions/f8099d56-e7c7-45b0-88e1-ee2af34ebfa0

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_transLat_mono
import Theorems.Thm_Formalism_L2_DIV_delStd_le_nabStd

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
theorem _root_.solution : DelLeNab := by
  intro K _ _ ι _ n lam M
  exact Submodule.comap_mono (transLat_mono lam (delStd_le_nabStd K lam) M)
end Formalism.L2.DIV
