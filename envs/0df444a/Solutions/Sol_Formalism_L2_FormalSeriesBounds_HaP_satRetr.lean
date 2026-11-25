-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.HaP.satRetr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:34:21.158868+00:00
-- url     : https://prove2.me/submissions/22eae841-49db-466b-9140-6eabb9a350b3

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaLeaves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj
namespace Formalism.L2.FormalSeriesBounds.HaP
theorem _root_.solution : SatRetrSt := by
  intro ι _ W hW
  haveI : NoZeroSMulDivisors ℤ ((ι → ℤ) ⧸ W) := by
    refine ⟨fun {z x} h => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective W x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    by_cases hz : z = 0
    · exact Or.inl hz
    · right
      rw [Submodule.Quotient.mk_eq_zero]
      exact hW z x hz h
  haveI : Module.Free ℤ ((ι → ℤ) ⧸ W) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property W.mkQ LinearMap.id (Submodule.mkQ_surjective W)
  have hs' : ∀ y, W.mkQ (s y) = y := fun y => by rw [← LinearMap.comp_apply, hs, LinearMap.id_apply]
  refine ⟨(LinearMap.id - s ∘ₗ W.mkQ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ)), fun x => ?_, fun x hx => ?_⟩
  · have h1 : W.mkQ ((LinearMap.id - s ∘ₗ W.mkQ : (ι → ℤ) →ₗ[ℤ] (ι → ℤ)) x) = 0 := by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs', sub_self]
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
  · have h0 : W.mkQ x = 0 := by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hx
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0, map_zero, sub_zero]
end Formalism.L2.FormalSeriesBounds.HaP
