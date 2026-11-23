-- Prove2me | solution 1 for Formalism.L2.Th1.A.IsDer.map_ofNat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:14.079649+00:00
-- url     : https://prove2.me/submissions/239a01d9-b4b0-479a-9fd8-a349933acf09

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_natCast

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
open Formalism.L2.Th1.A.IsDer
variable {A : Type u} [CommRing A] {D : A → A}
namespace Formalism.L2.Th1.A.IsDer
theorem _root_.solution (h : IsDer D) (n : ℕ) [n.AtLeastTwo] : D (OfNat.ofNat n : A) = 0 := by
  have h1 := h.map_natCast (OfNat.ofNat n)
  rwa [Nat.cast_ofNat] at h1
end Formalism.L2.Th1.A.IsDer
