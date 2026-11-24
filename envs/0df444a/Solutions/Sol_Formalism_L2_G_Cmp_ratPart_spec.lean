-- Prove2me | solution 1 for Formalism.L2.G.Cmp.ratPart_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:58:12.196973+00:00
-- url     : https://prove2.me/submissions/b6418baa-77c5-42a5-b1df-11a0c2575024

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_IsComplRatCompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
variable {LL Kf : Type*} [Field LL] [Field Kf] {e : LL →+* Kf}
  {V0 V1 W0 W1 ι : Type*} [AddCommGroup V0] [Module LL V0] [AddCommGroup V1] [Module LL V1]
  [AddCommGroup W0] [Module Kf W0] [AddCommGroup W1] [Module Kf W1]
variable {Cc : Type*} [Field Cc] {s : LL →+* Cc} {M0 M1 : Type*} [AddCommGroup M0] [Module Cc M0]
  [AddCommGroup M1] [Module Cc M1]
namespace Formalism.L2.G.Cmp
theorem _root_.solution (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (hinj : Function.Injective e1) (f : M0 →ₗ[Cc] M1)
    (x : ratDom e0 e1 f) : e1 (ratPart e0 e1 hinj f x) = f (e0 x) := Classical.choose_spec x.2
end Formalism.L2.G.Cmp
