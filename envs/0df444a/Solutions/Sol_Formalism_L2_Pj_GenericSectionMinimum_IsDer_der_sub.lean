-- Prove2me | solution 1 for Formalism.L2.Pj.GenericSectionMinimum.IsDer.der_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:23:14.211801+00:00
-- url     : https://prove2.me/submissions/f6d0f1e7-4d8f-45d4-b663-f9cdd9d5f41b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Theorems.Thm_Formalism_L2_Pj_GenericSectionMinimum_IsDer_der_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open Formalism.L2.Pj.GenericSectionMinimum.IsDer
variable {A : Type*} [CommRing A] {δ : A → A}
namespace Formalism.L2.Pj.GenericSectionMinimum.IsDer
theorem _root_.solution (h : IsDer δ) (x y : A) : δ (x - y) = δ x - δ y := by
  rw [sub_eq_add_neg, h.add, h.der_neg, sub_eq_add_neg]
end Formalism.L2.Pj.GenericSectionMinimum.IsDer
