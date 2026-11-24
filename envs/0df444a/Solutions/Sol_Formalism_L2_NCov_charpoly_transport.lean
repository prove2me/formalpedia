-- Prove2me | solution 1 for Formalism.L2.NCov.charpoly_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:28:36.772819+00:00
-- url     : https://prove2.me/submissions/e61316ba-06d7-44aa-abae-45257dd6439c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverPoly
import Theorems.Thm_Formalism_L2_NCov_charpoly_transport_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.NCov
open Module
variable {K₁ K₂ V₁ V₂ : Type*} [Field K₁] [Field K₂] [AddCommGroup V₁] [Module K₁ V₁] [AddCommGroup V₂]
  [Module K₂ V₂]
namespace Formalism.L2.NCov
theorem _root_.solution [Module.Finite K₁ V₁] [Module.Finite K₂ V₂] (σ : K₁ →+* K₂) (ι : V₁ →ₛₗ[σ] V₂) {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K₁ V₁) (hli : LinearIndependent K₂ (ι ∘ b))
    (hsp : Submodule.span K₂ (Set.range (ι ∘ b)) = ⊤) (A₁ : Module.End K₁ V₁) (A₂ : Module.End K₂ V₂)
    (h : ∀ x, A₂ (ι x) = ι (A₁ x)) :
    A₂.charpoly = A₁.charpoly.map σ :=
  charpoly_transport_basis σ ι b hli hsp A₁ A₂ fun a => h (b a)
end Formalism.L2.NCov
