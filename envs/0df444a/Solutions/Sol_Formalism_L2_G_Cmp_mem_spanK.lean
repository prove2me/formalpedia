-- Prove2me | solution 1 for Formalism.L2.G.Cmp.mem_spanK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:58:11.365798+00:00
-- url     : https://prove2.me/submissions/221b0834-4fd2-40e1-8a2b-231688dd50a7

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
namespace Formalism.L2.G.Cmp
theorem _root_.solution (c0 : V0 →ₛₗ[e] W0) (x : V0) : c0 x ∈ spanK c0 := Submodule.subset_span ⟨x, rfl⟩
end Formalism.L2.G.Cmp
