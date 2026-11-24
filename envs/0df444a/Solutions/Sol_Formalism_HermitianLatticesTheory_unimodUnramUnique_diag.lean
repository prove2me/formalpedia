-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.unimodUnramUnique_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:49:18.6318+00:00
-- url     : https://prove2.me/submissions/950808de-ebcf-4289-ae8f-57114910810f

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementJac
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_hermFix
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_offdiag
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_scale
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_transv

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
    (hR₀ : ∀ x, x ∈ R₀ ↔ star x = x) {θ : R} (hθ : IsUnit (θ - star θ))
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι R) (hA : Aᴴ = A)
    (hdet : IsUnit A.det) : ∃ g : Matrix ι ι R, IsUnit g.det ∧ ∃ i, (gᴴ * A * g) i i = 1 := by
  by_cases h : ∃ i, IsUnit (A i i)
  · obtain ⟨i, hi⟩ := h
    obtain ⟨g, hg, hgi⟩ := unimodUnramUnique_scale hR₀ hθ A hA i hi
    exact ⟨g, hg, i, hgi⟩
  · push Not at h
    obtain ⟨i, j, c, hij, hc⟩ := unimodUnramUnique_offdiag hR₀ hθ A hA hdet h
    set g₁ := transvection j i c with hg₁def
    set B := g₁ᴴ * A * g₁ with hBdef
    have hB : Bᴴ = B := by simp [hBdef, conjTranspose_mul, hA, Matrix.mul_assoc]
    have hBi : IsUnit (B i i) := by
      rw [hBdef, hg₁def, unimodUnramUnique_transv A i j c]
      have hji : A j i = star (A i j) := (unimodUnramUnique_hermFix A hA j i).symm
      have hfi := unimodUnramUnique_hermFix A hA i i
      have hfj := unimodUnramUnique_hermFix A hA j j
      have e : A i i + (c * A i j + star c * A j i) + star c * c * A j j
          = (c * A i j + star (c * A i j)) + (A i i + star c * c * A j j) := by
        rw [star_mul, ← hji]; ring
      rw [e]
      have hfy : star (A i i + star c * c * A j j) = A i i + star c * c * A j j := by
        simp only [star_add, star_mul, star_star, hfi, hfj]; ring
      have hy : ¬ IsUnit (A i i + star c * c * A j j) := by
        intro hy
        have hfz : star (star c * c * A j j) = star c * c * A j j := by
          simp only [star_mul, star_star, hfj]; ring
        rcases unimodUnramUnique_unitAdd hR₀ hfi hfz hy with h1 | h1
        · exact h i h1
        · exact h j (isUnit_of_mul_isUnit_right h1)
      by_contra hn
      have hsum : IsUnit ((c * A i j + star (c * A i j) + (A i i + star c * c * A j j))
          + -(A i i + star c * c * A j j)) := by rw [add_neg_cancel_right]; exact hc
      have hfs : star (c * A i j + star (c * A i j) + (A i i + star c * c * A j j))
          = c * A i j + star (c * A i j) + (A i i + star c * c * A j j) := by
        rw [star_add, unimodUnramUnique_trFix, hfy]
      have hfn : star (-(A i i + star c * c * A j j)) = -(A i i + star c * c * A j j) := by
        rw [star_neg, hfy]
      rcases unimodUnramUnique_unitAdd hR₀ hfs hfn hsum with h1 | h1
      · exact hn h1
      · exact hy (IsUnit.neg_iff _ |>.1 h1)
    obtain ⟨g₂, hg₂, hg₂i⟩ := unimodUnramUnique_scale hR₀ hθ B hB i hBi
    refine ⟨g₁ * g₂, ?_, i, ?_⟩
    · rw [det_mul, hg₁def, det_transvection_of_ne j i (Ne.symm hij), one_mul]; exact hg₂
    · rw [← hg₂i, hBdef]; simp [conjTranspose_mul, Matrix.mul_assoc]
end Formalism.HermitianLatticesTheory
