-- Prove2me | solution 1 for Formalism.L2.Pj.vG_incG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:16:49.372811+00:00
-- url     : https://prove2.me/submissions/307babd7-d92f-4f76-8d99-55db4b72c7e9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf
import Theorems.Thm_Formalism_L2_Pj_vG_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
variable {K R M W : Type} [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (key : W → M)
  (C : W → Submodule K R)
variable {v : R → EReal}
namespace Formalism.L2.Pj
theorem _root_.solution (h0 : v 0 = ⊤) (w : W) (F : C w) : vG v (incG key C w F) = v F := vG_single h0 _ _
end Formalism.L2.Pj
