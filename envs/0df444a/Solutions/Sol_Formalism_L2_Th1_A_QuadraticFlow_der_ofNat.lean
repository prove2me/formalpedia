-- Prove2me | solution 1 for Formalism.L2.Th1.A.QuadraticFlow.der_ofNat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:48.406074+00:00
-- url     : https://prove2.me/submissions/009fd281-207b-4ad0-bed9-4c8583a65a5b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_der_natCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.QuadraticFlow
variable {A : Type u} [CommRing A] {D : A → A}
namespace Formalism.L2.Th1.A.QuadraticFlow
theorem _root_.solution (h : IsDer D) (n : ℕ) [n.AtLeastTwo] : D (OfNat.ofNat n : A) = 0 := by
  simpa using der_natCast h (OfNat.ofNat n)
end Formalism.L2.Th1.A.QuadraticFlow
