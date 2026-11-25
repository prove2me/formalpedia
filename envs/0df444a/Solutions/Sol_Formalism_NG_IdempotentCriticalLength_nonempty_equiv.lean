-- Prove2me | solution 1 for Formalism.NG.IdempotentCriticalLength.nonempty_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:18:37.706884+00:00
-- url     : https://prove2.me/submissions/fdd5b250-c8e1-470e-88c3-cc9d016ec93c

import Definitions.Def_Formalism_CharacterColumnKernels_StatCompMultSimple
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEpsImgEqAdd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SmulEqZeroIffCrit
import Theorems.Thm_Formalism_NG_IdempotentCriticalLength_smul_eq_zero_iff_crit
import Theorems.Thm_Formalism_NG_epsMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.NG.epsMap_apply



set_option autoImplicit false
open Classical
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentCriticalLength
variable {O Λ : Type*} [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]
namespace Formalism.NG.IdempotentCriticalLength
theorem _root_.solution {V W : Type*} [AddCommGroup V] [Module Λ V] [IsSimpleModule Λ V]
    [AddCommGroup W] [Module Λ W] [IsSimpleModule Λ W] {ε : Λ} (hε : IsIdempotentElem ε)
    (hii : ∀ x : Λ, ∃ c : O, ε * x * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ)
    (hiii : ∀ c ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ c ∈ Ring.jacobson Λ)
    (hV : ∃ t : V, ε • t ≠ 0) (hW : ∃ s : W, ε • s ≠ 0) : Nonempty (V ≃ₗ[Λ] W) := by
  obtain ⟨t, ht⟩ := hV
  obtain ⟨s, hs⟩ := hW
  have hv : ε • (ε • t) = ε • t := by rw [← mul_smul, hε.eq]
  have hu : ε • (ε • s) = ε • s := by rw [← mul_smul, hε.eq]
  have hker : LinearMap.ker (LinearMap.toSpanSingleton Λ V (ε • t)) =
      LinearMap.ker (LinearMap.toSpanSingleton Λ W (ε • s)) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    rw [smul_eq_zero_iff_crit hii hiii ht hv, smul_eq_zero_iff_crit hii hiii hs hu]
  exact ⟨(LinearMap.quotKerEquivOfSurjective _
      (IsSimpleModule.toSpanSingleton_surjective Λ ht)).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans
      (LinearMap.quotKerEquivOfSurjective _ (IsSimpleModule.toSpanSingleton_surjective Λ hs)))⟩
end Formalism.NG.IdempotentCriticalLength
