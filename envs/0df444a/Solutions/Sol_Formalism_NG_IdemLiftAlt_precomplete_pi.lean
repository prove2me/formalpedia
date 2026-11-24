-- Prove2me | solution 1 for Formalism.NG.IdemLiftAlt.precomplete_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:09:43.734489+00:00
-- url     : https://prove2.me/submissions/0a88bca8-f32c-44c4-b7bb-1bf3fecc3afd

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdemLiftAlt
variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]
namespace Formalism.NG.IdemLiftAlt
theorem _root_.solution (I : Ideal O) [IsNoetherianRing O] [IsAdicComplete I O] (n : ℕ) :
    IsPrecomplete I (Fin n → O) := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ :=
    (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I (Fin n → O)).2 y
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨c, rfl⟩ := AdicCompletion.of_surjective I O r
    refine ⟨c • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    have hc : AdicCompletion.of I O c = algebraMap O (AdicCompletion I O) c := by
      rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]
    rw [hc, algebraMap_smul]
  | add u v hu hv =>
    obtain ⟨p, hp⟩ := hu
    obtain ⟨q, hq⟩ := hv
    exact ⟨p + q, by rw [map_add, map_add, hp, hq]⟩
end Formalism.NG.IdemLiftAlt
