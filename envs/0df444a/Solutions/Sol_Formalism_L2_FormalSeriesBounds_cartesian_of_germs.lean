-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.cartesian_of_germs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:10:56.990276+00:00
-- url     : https://prove2.me/submissions/0ee6f0f3-21df-4979-8531-df91d66650fd

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartTop
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_addCvFB_of
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_cartFB_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (hPT : PTFBSt) (hG : GermIAllSt) (hStab : HStabFBSt) : CartFBSt :=
  cartFB_of hPT (addCvFB_of hG) hStab
end Formalism.L2.FormalSeriesBounds
