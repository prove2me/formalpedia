-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.exists_equiv_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:02.878562+00:00
-- url     : https://prove2.me/submissions/6d9a09b5-e7b7-4289-9c5c-28e3db903c0a

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module
variable {K : Type*} [Field K]
namespace Formalism.FourierDecayAlt.P.S3x4
theorem _root_.solution {A V : Type*} [AddCommGroup A] [Module K A] [AddCommGroup V] [Module K V]
    [FiniteDimensional K A] (i i' : A →ₗ[K] V) (hi : Function.Injective i)
    (hi' : Function.Injective i') : ∃ g : V ≃ₗ[K] V, ∀ x, g (i x) = i' x := by
  let f : LinearMap.range i ≃ₗ[K] LinearMap.range i' :=
    (LinearEquiv.ofInjective i hi).symm ≪≫ₗ LinearEquiv.ofInjective i' hi'
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, fun x => ?_⟩
  have h1 := hg ⟨i x, LinearMap.mem_range_self i x⟩
  have h2 : (LinearEquiv.ofInjective i hi).symm ⟨i x, LinearMap.mem_range_self i x⟩ = x := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [f, LinearEquiv.trans_apply, h2] at h1
  rw [← h1]; rfl
end Formalism.FourierDecayAlt.P.S3x4
