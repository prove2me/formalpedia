-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.length_quot_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:00:47.739499+00:00
-- url     : https://prove2.me/submissions/2e1f016f-b283-4d62-bd98-10174919c9c5

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_ord_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
open Formalism.IrreducibleCountingLemmas.TW.Idx
variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
namespace Formalism.IrreducibleCountingLemmas.TW.Idx
theorem _root_.solution {B ι : Type} [AddCommGroup B] [Module O B] [Fintype ι]
    (b : Basis ι O B) (f : B →ₗ[O] B) (hf : Function.Injective f) :
    Module.length O (B ⧸ LinearMap.range f) = Ring.ord O (LinearMap.det f) := by
  classical
  have h : finrank O (LinearMap.range f) = finrank O B :=
    (LinearEquiv.ofInjective f hf).finrank_eq.symm
  rw [(Submodule.quotientEquivPiSpan _ b h).length_eq, Module.length_pi_of_fintype]
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  have hne := Submodule.smithNormalFormCoeffs_ne_zero b h
  generalize Submodule.smithNormalFormCoeffs b h = a at *
  generalize Submodule.smithNormalFormTopBasis b h = b' at *
  generalize Submodule.smithNormalFormBotBasis b h = ab at *
  let e' : B ≃ₗ[O] LinearMap.range f := b'.equiv ab (Equiv.refl _)
  have hass : Associated (LinearMap.det f)
      (LinearMap.det ((LinearMap.range f).subtype ∘ₗ (e' : B →ₗ[O] LinearMap.range f))) := by
    have := LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype
      (LinearEquiv.ofInjective f hf) e'
    convert this using 2
    ext x; rfl
  have hg : LinearMap.det ((LinearMap.range f).subtype ∘ₗ (e' : B →ₗ[O] LinearMap.range f))
      = ∏ i, a i := by
    have : (LinearMap.range f).subtype ∘ₗ (e' : B →ₗ[O] LinearMap.range f)
        = Matrix.toLin b' b' (Matrix.diagonal a) := by
      apply b'.ext; intro i
      simp [e', ab_eq, Matrix.toLin_self, Matrix.diagonal_apply]
    rw [this, LinearMap.det_toLin, Matrix.det_diagonal]
  rw [Ring.ord_eq_of_associated hass, hg, ord_prod _ _ hne]
  rfl
end Formalism.IrreducibleCountingLemmas.TW.Idx
