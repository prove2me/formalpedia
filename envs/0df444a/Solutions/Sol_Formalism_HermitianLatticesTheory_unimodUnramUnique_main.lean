-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:56:17.014907+00:00
-- url     : https://prove2.me/submissions/27f67940-e15c-4e17-9798-d9a3d7d7e540

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_diag
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_block
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_transport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
open Polynomial IsLocalRing Matrix
variable {R : Type} [CommRing R] [StarRing R] {R₀ : Subring R}
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution [HenselianLocalRing R₀] [Finite (ResidueField R₀)]
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ)) (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
      ∀ A : Matrix ι ι R, Aᴴ = A → IsUnit A.det →
        ∃ g : Matrix ι ι R, IsUnit g.det ∧ gᴴ * A * g = 1 := by
  induction n with
  | zero =>
    intro ι _ _ hc A _ _
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hc
    exact ⟨1, by simp, by ext i; exact isEmptyElim i⟩
  | succ n ih =>
    intro ι _ _ hc A hA hdet
    have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨g₁, hg₁, i, hi⟩ := unimodUnramUnique_diag hR₀ hθ A hA hdet
    set B := g₁ᴴ * A * g₁ with hBdef
    have hB : Bᴴ = B := by simp [hBdef, conjTranspose_mul, hA, Matrix.mul_assoc]
    have hBdet : IsUnit B.det := by
      rw [hBdef, det_mul, det_mul, det_conjTranspose]; exact (hg₁.star.mul hdet).mul hg₁
    let κ := {j // j ≠ i}
    have hκ : Fintype.card κ = n := by
      have := Fintype.card_subtype_compl (fun j => j = i)
      simp only [Fintype.card_subtype_eq, hc] at this
      simpa [κ] using this
    let e : Unit ⊕ κ ≃ ι :=
      { toFun := Sum.elim (fun _ => i) Subtype.val
        invFun := fun j => if h : j = i then Sum.inl () else Sum.inr ⟨j, h⟩
        left_inv := by
          rintro (⟨⟩ | ⟨j, hj⟩)
          · simp
          · simp [hj]
        right_inv := by intro j; by_cases h : j = i <;> simp [h] }
    have hB' : (B.submatrix e e)ᴴ = B.submatrix e e := by rw [conjTranspose_submatrix, hB]
    have hB'det : IsUnit (B.submatrix e e).det := by rw [det_submatrix_equiv_self]; exact hBdet
    have hB'1 : B.submatrix e e (Sum.inl ()) (Sum.inl ()) = 1 := hi
    obtain ⟨g₂, hg₂, hg₂e⟩ := unimodUnramUnique_block (ih κ hκ) _ hB' hB'det hB'1
    refine ⟨g₁ * g₂.submatrix e.symm e.symm, ?_, ?_⟩
    · rw [det_mul, det_submatrix_equiv_self]; exact hg₁.mul hg₂
    · have := unimodUnramUnique_transport e B g₂ hg₂e
      rw [← this, hBdef]; simp [conjTranspose_mul, Matrix.mul_assoc]
end Formalism.HermitianLatticesTheory
