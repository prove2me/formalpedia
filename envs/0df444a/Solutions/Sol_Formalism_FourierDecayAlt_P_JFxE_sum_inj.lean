-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.sum_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:54.835411+00:00
-- url     : https://prove2.me/submissions/9b46ff9f-72b3-4540-af48-74e286828653

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {M : Type*} [AddCommMonoid M] {t : ℕ} (e : Fin t ≃ Fin n) (F : (Fin t → Fin n) → M)
    (hF : ∀ α, ¬ Function.Injective α → F α = 0) :
    ∑ α, F α = ∑ γ : Equiv.Perm (Fin t), F (e ∘ γ) := by
  classical
  have himg : ∑ α ∈ (Finset.univ.image fun γ : Equiv.Perm (Fin t) => (e ∘ γ : Fin t → Fin n)), F α = ∑ α, F α := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro α _ hα
    apply hF
    intro hinj
    apply hα
    have hi : Function.Injective (e.symm ∘ α) := e.symm.injective.comp hinj
    have hs : Function.Surjective (e.symm ∘ α) := Finite.injective_iff_surjective.mp hi
    refine Finset.mem_image.mpr ⟨Equiv.ofBijective _ ⟨hi, hs⟩, Finset.mem_univ _, ?_⟩
    funext j
    show e ((e.symm ∘ α) j) = α j
    simp
  rw [← himg, Finset.sum_image]
  intro γ₁ _ γ₂ _ h
  exact Equiv.ext fun j => by have := congrFun h j; simpa using this
end Formalism.FourierDecayAlt.P.JFxE
