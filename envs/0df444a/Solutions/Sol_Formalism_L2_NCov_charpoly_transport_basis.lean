-- Prove2me | solution 1 for Formalism.L2.NCov.charpoly_transport_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:19:28.38583+00:00
-- url     : https://prove2.me/submissions/1db47292-15ee-499c-8fea-b45b046c0191

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverPoly
import Theorems.Thm_Formalism_L2_NCov_repr_transport

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
    (h : ∀ a, A₂ (ι (b a)) = ι (A₁ (b a))) :
    A₂.charpoly = A₁.charpoly.map σ := by
  have hM : LinearMap.toMatrix (Module.Basis.mk hli hsp.ge) (Module.Basis.mk hli hsp.ge) A₂ =
      (LinearMap.toMatrix b b A₁).map σ := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
      Module.Basis.mk_apply, Function.comp_apply, h j, repr_transport σ ι b hli hsp]
  rw [← LinearMap.charpoly_toMatrix A₂ (Module.Basis.mk hli hsp.ge), hM, Matrix.charpoly_map,
    LinearMap.charpoly_toMatrix]
end Formalism.L2.NCov
