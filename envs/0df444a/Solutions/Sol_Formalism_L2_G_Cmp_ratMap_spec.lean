-- Prove2me | solution 1 for Formalism.L2.G.Cmp.ratMap_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:08:47.804922+00:00
-- url     : https://prove2.me/submissions/848f1738-7b68-4172-b07c-bb487c18f2c3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_IsComplRatCompl
import Theorems.Thm_Formalism_L2_G_Cmp_ratMap_eq

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
    (h : ∀ x, ∃ y, e1 y = f (e0 x)) (x : V0) : e1 (ratMap e0 e1 hinj f x) = f (e0 x) := by
  obtain ⟨y, hy⟩ := h x
  rw [ratMap_eq e0 e1 hinj f x y hy]
  exact hy
end Formalism.L2.G.Cmp
