-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.coeff_wCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:39.132621+00:00
-- url     : https://prove2.me/submissions/bf72a0d5-3031-4645-ad5d-9fcf01d9c684

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported

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
theorem _root_.solution (w : Set ι) (M ν : ι × Fin n →₀ ℕ) (P : MvPolynomial (ι × Fin n) R) :
    coeff ν (wCoeff w M P) =
      if ν.filter (fun v => v.1 ∈ w) = 0 ∧ M.filter (fun v => v.1 ∉ w) = 0 then coeff (M + ν) P else 0 := by
  unfold wCoeff
  rw [coeff_sum]
  simp only [coeff_monomial]
  have key : ∀ μ : ι × Fin n →₀ ℕ, (μ.filter (fun v => v.1 ∈ w) = M ∧ μ.filter (fun v => v.1 ∉ w) = ν) ↔
      (μ = M + ν ∧ ν.filter (fun v => v.1 ∈ w) = 0 ∧ M.filter (fun v => v.1 ∉ w) = 0) := by
    intro μ
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [← h1, ← h2, Finsupp.filter_pos_add_filter_neg]
      · rw [← h2]; ext x
        simp only [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
        split_ifs <;> simp_all
      · rw [← h1]; ext x
        simp only [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
        split_ifs <;> simp_all
    · rintro ⟨rfl, h2, h3⟩
      refine ⟨?_, ?_⟩
      · rw [Finsupp.filter_add, h2, add_zero]
        have := Finsupp.filter_pos_add_filter_neg M (fun v => v.1 ∈ w)
        rw [h3, add_zero] at this
        exact this
      · rw [Finsupp.filter_add, h3, zero_add]
        have := Finsupp.filter_pos_add_filter_neg ν (fun v => v.1 ∈ w)
        rw [h2, zero_add] at this
        exact this
  split_ifs with hc
  · by_cases hm : M + ν ∈ P.support
    · rw [Finset.sum_eq_single (M + ν)]
      · rw [if_pos ((key _).2 ⟨rfl, hc⟩).2]
      · intro μ hμ hne
        rw [Finset.mem_filter] at hμ
        rw [if_neg]
        intro h2
        exact hne ((key μ).1 ⟨hμ.2, h2⟩).1
      · intro h; exact absurd (Finset.mem_filter.2 ⟨hm, ((key _).2 ⟨rfl, hc⟩).1⟩) h
    · rw [MvPolynomial.notMem_support_iff.1 hm]
      refine Finset.sum_eq_zero fun μ hμ => ?_
      rw [Finset.mem_filter] at hμ
      rw [if_neg]
      intro h2
      have := ((key μ).1 ⟨hμ.2, h2⟩).1
      subst this
      exact hm hμ.1
  · refine Finset.sum_eq_zero fun μ hμ => ?_
    rw [Finset.mem_filter] at hμ
    rw [if_neg]
    intro h2
    exact hc ((key μ).1 ⟨hμ.2, h2⟩).2
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
