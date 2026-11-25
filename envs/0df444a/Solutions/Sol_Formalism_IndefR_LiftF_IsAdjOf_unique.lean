-- Prove2me | solution 1 for Formalism.IndefR.LiftF.IsAdjOf.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:05:19.935433+00:00
-- url     : https://prove2.me/submissions/e30e2301-8da3-41d1-916f-dd0db610697f

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DatumF
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HasInfExpF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.IndefR Formalism.IndefR.LiftF
variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
namespace Formalism.IndefR.LiftF
namespace IsAdjOf
theorem _root_.solution {ipM : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ} {ipN : N →ₗ[ℂ] N →ₗ⋆[ℂ] ℂ} {A : M →ₗ[ℂ] N}
    {B B' : N →ₗ[ℂ] M} (hnd : ∀ z, (∀ x, ipM x z = 0) → z = 0)
    (h : IsAdjOf ipM ipN A B) (h' : IsAdjOf ipM ipN A B') : B = B' := by
  refine LinearMap.ext fun y => sub_eq_zero.1 (hnd _ fun x => ?_)
  rw [map_sub, ← h x y, ← h' x y, sub_self]
end IsAdjOf
end Formalism.IndefR.LiftF
