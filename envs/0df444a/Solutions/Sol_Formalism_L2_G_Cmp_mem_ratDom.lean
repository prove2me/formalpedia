-- Prove2me | solution 1 for Formalism.L2.G.Cmp.mem_ratDom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:58:10.425796+00:00
-- url     : https://prove2.me/submissions/27808e57-a55a-49d7-80dc-3993d6d7ddf6

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
theorem _root_.solution (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (f : M0 →ₗ[Cc] M1) (x : V0) :
    x ∈ ratDom e0 e1 f ↔ ∃ y, e1 y = f (e0 x) := Iff.rfl
end Formalism.L2.G.Cmp
