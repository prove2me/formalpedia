-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubicFlow.cubic_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:21.410052+00:00
-- url     : https://prove2.me/submissions/6dec3171-5564-4b96-9060-eea6e9972a05

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowThird

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
open Formalism.L2.Th1.A.CubicFlow
open QuadraticFlow
variable {A : Type u} [CommRing A]
namespace Formalism.L2.Th1.A.CubicFlow
theorem _root_.solution [IsDomain A] {C3 C2 C1 C0 z1 z2 z3 : A} (hz : z1 ≠ z2)
    (h1 : C3 * z1 ^ 3 + C2 * z1 ^ 2 + C1 * z1 + C0 = 0)
    (h2 : C3 * z2 ^ 3 + C2 * z2 ^ 2 + C1 * z2 + C0 = 0)
    (he1 : C3 * (z1 + z2 + z3) + C2 = 0) :
    C3 * z3 ^ 3 + C2 * z3 ^ 2 + C1 * z3 + C0 = 0 ∧
      C3 * (z1 * z2 + z1 * z3 + z2 * z3) - C1 = 0 ∧ C3 * (z1 * z2 * z3) + C0 = 0 := by
  have hq : (z1 - z2) * (C3 * (z1 ^ 2 + z1 * z2 + z2 ^ 2) + C2 * (z1 + z2) + C1) = 0 := by
    linear_combination h1 - h2
  have hq' := (mul_eq_zero.mp hq).resolve_left (sub_ne_zero.mpr hz)
  have e2 : C3 * (z1 * z2 + z1 * z3 + z2 * z3) - C1 = 0 := by
    linear_combination -hq' + (z1 + z2) * he1
  have e3 : C3 * (z1 * z2 * z3) + C0 = 0 := by
    linear_combination h1 - z1 ^ 2 * he1 + z1 * e2
  refine ⟨?_, e2, e3⟩
  linear_combination z3 ^ 2 * he1 - z3 * e2 + e3
end Formalism.L2.Th1.A.CubicFlow
