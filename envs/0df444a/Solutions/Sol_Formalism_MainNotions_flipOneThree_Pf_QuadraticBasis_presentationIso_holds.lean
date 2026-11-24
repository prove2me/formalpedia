-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.presentationIso_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:32:54.231464+00:00
-- url     : https://prove2.me/submissions/2e3bc3fc-a3ac-415d-a5e4-b95377a0e832

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_PresIso
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_pbE_mul
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_pbE_add
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_pbE_bij
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
section
variable {W O : Type} [CommRing W] [CommRing O]
end
private theorem pbF_pbM_eq_pbM_map {W₁ W₂ : Type} [CommRing W₁] [CommRing W₂] (φ : W₁ ≃+* W₂)
    (f0 f1 ϖ : W₁) (t s : W₁ × W₁ × W₁ × W₁) :
    pbF φ (pbM f0 f1 ϖ t s) = pbM (φ f0) (φ f1) (φ ϖ) (pbF φ t) (pbF φ s) := by
  simp [pbF, pbM]
private theorem pbF_add {W₁ W₂ : Type} [CommRing W₁] [CommRing W₂] (φ : W₁ ≃+* W₂)
    (t s : W₁ × W₁ × W₁ × W₁) : pbF φ (t + s) = pbF φ t + pbF φ s := by
  simp [pbF]
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
end

set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
theorem _root_.solution : PresIso := by
  intro W₁ W₂ O₁ O₂ _ _ _ _ j₁ j₂ θ₁ w₁ θ₂ w₂ f0 f1 ϖ φW hθ₁ hθ₂ hw₁ hw₂ hB₁ hB₂
  let e₁ : (W₁ × W₁ × W₁ × W₁) ≃ O₁ := Equiv.ofBijective _ (pbE_bij hB₁)
  let e₂ : (W₂ × W₂ × W₂ × W₂) ≃ O₂ := Equiv.ofBijective _ (pbE_bij hB₂)
  let eF : (W₁ × W₁ × W₁ × W₁) ≃ (W₂ × W₂ × W₂ × W₂) :=
    { toFun := pbF φW
      invFun := pbF φW.symm
      left_inv := fun t => by simp [pbF]
      right_inv := fun t => by simp [pbF] }
  let E : O₁ ≃ O₂ := (e₁.symm.trans eF).trans e₂
  have hE : ∀ t, E (pbE j₁ θ₁ w₁ t) = pbE j₂ θ₂ w₂ (pbF φW t) := by
    intro t
    have h1 : e₁.symm (pbE j₁ θ₁ w₁ t) = t := e₁.symm_apply_apply t
    simp only [E, Equiv.trans_apply, h1]
    rfl
  have hsurj : ∀ x : O₁, ∃ t, x = pbE j₁ θ₁ w₁ t :=
    fun x => ⟨e₁.symm x, (e₁.apply_symm_apply x).symm⟩
  refine ⟨{ E with
    map_mul' := ?_
    map_add' := ?_ }, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨t, rfl⟩ := hsurj x
    obtain ⟨s, rfl⟩ := hsurj y
    show E _ = E _ * E _
    rw [pbE_mul j₁ θ₁ w₁ f0 f1 ϖ hθ₁ hw₁, hE, hE, hE, pbF_pbM_eq_pbM_map,
      pbE_mul j₂ θ₂ w₂ (φW f0) (φW f1) (φW ϖ) hθ₂ hw₂]
  · intro x y
    obtain ⟨t, rfl⟩ := hsurj x
    obtain ⟨s, rfl⟩ := hsurj y
    show E _ = E _ + E _
    rw [pbE_add, hE, hE, hE, pbF_add, pbE_add]
  · intro x
    have h1 := hE (x, 0, 0, 0)
    rw [show pbE j₁ θ₁ w₁ (x, 0, 0, 0) = j₁ x by simp [pbE]] at h1
    show E (j₁ x) = j₂ (φW x)
    rw [h1]
    simp [pbE, pbF]
  · have h1 := hE (0, 0, 1, 0)
    rw [show pbE j₁ θ₁ w₁ (0, 0, 1, 0) = w₁ by simp [pbE]] at h1
    show E w₁ = w₂
    rw [h1]
    simp [pbE, pbF]
  · have h1 := hE (0, 1, 0, 0)
    rw [show pbE j₁ θ₁ w₁ (0, 1, 0, 0) = θ₁ by simp [pbE]] at h1
    show E θ₁ = θ₂
    rw [h1]
    simp [pbE, pbF]
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
