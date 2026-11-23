-- Prove2me | solution 1 for Formalism.L2.Th1.A.IsDer.map_intCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:48.454748+00:00
-- url     : https://prove2.me/submissions/2a263d4b-c24f-41f9-8c29-6466ce76e092

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
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
theorem _root_.solution (h : IsDer D) (n : ℤ) : D (n : A) = 0 := by
  rcases n with n | n
  · rw [Int.ofNat_eq_coe, Int.cast_natCast]
    exact h.map_natCast n
  · rw [Int.cast_negSucc, h.map_neg, h.map_natCast, neg_zero]
end Formalism.L2.Th1.A.IsDer
