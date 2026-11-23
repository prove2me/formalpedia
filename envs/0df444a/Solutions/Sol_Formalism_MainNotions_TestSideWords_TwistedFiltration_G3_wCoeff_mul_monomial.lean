-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.wCoeff_mul_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:41.061876+00:00
-- url     : https://prove2.me/submissions/5f4eab09-b566-4774-9a9f-b5451d97a65c

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_coeff_wCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
open Classical
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
theorem _root_.solution (w : Set ι) (M M' : ι × Fin n →₀ ℕ) (P : MvPolynomial (ι × Fin n) R) (hP : WFree w P)
    (hM' : M'.filter (fun v => v.1 ∉ w) = 0) :
    wCoeff w M (P * monomial M' 1) = if M' = M then P else 0 := by
  classical
  have hM'x : ∀ x, x.1 ∉ w → M' x = 0 := by
    intro x hx
    have : (M'.filter (fun v => v.1 ∉ w)) x = 0 := by rw [hM']; rfl
    rwa [Finsupp.filter_apply, if_pos hx] at this
  have hPz : ∀ ρ : ι × Fin n →₀ ℕ, (∃ x, x.1 ∈ w ∧ ρ x ≠ 0) → coeff ρ P = 0 := by
    rintro ρ ⟨x, hx, hρ⟩
    by_contra hne
    have h1 := hP ρ (MvPolynomial.mem_support_iff.2 hne)
    have : (ρ.filter (fun v => v.1 ∈ w)) x = 0 := by rw [h1]; rfl
    rw [Finsupp.filter_apply, if_pos hx] at this
    exact hρ this
  ext ν
  rw [coeff_wCoeff, coeff_mul_monomial']
  split_ifs with hc h1 h2 h2 h1 h1
  · subst h2
    rw [mul_one, add_tsub_cancel_left]
  · rw [mul_one]
    apply hPz
    have hMx : ∀ x, x.1 ∉ w → M x = 0 := by
      intro x hx
      have : (M.filter (fun v => v.1 ∉ w)) x = 0 := by rw [hc.2]; rfl
      rwa [Finsupp.filter_apply, if_pos hx] at this
    have hνx : ∀ x, x.1 ∈ w → ν x = 0 := by
      intro x hx
      have : (ν.filter (fun v => v.1 ∈ w)) x = 0 := by rw [hc.1]; rfl
      rwa [Finsupp.filter_apply, if_pos hx] at this
    have : ∃ x, M' x ≠ M x := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      exact h2 (Finsupp.ext hall)
    obtain ⟨x, hx⟩ := this
    have hxw : x.1 ∈ w := by
      by_contra hxw
      exact hx (by rw [hM'x x hxw, hMx x hxw])
    refine ⟨x, hxw, ?_⟩
    have hle := h1 x
    rw [Finsupp.add_apply, hνx x hxw, add_zero] at hle
    rw [Finsupp.tsub_apply, Finsupp.add_apply, hνx x hxw, add_zero]
    omega
  · exact absurd (by rw [h2]; exact le_self_add) h1
  · simp
  · subst h1
    by_cases hν : ν.filter (fun v => v.1 ∈ w) = 0
    · exact absurd ⟨hν, hM'⟩ hc
    · by_contra hne
      exact hν (hP ν (MvPolynomial.mem_support_iff.2 (Ne.symm hne)))
  · rfl
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
