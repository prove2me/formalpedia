-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.coeff_divDer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:50.568862+00:00
-- url     : https://prove2.me/submissions/019d9944-f304-42b1-bdfe-03c799846318

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne

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
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
theorem _root_.solution (be μ : ι × Fin n →₀ ℕ) (F : MvPolynomial (ι × Fin n) R) :
    coeff μ (divDer be F) = coeff (μ + be) F * ((be.prod fun k j => ((μ + be) k).choose j : ℕ) : R) := by
  classical
  rw [divDer, coeff_sum]
  rw [Finset.sum_congr rfl (g := fun m => if m = μ + be then
      coeff m F * ((be.prod fun k j => (m k).choose j : ℕ) : R) else 0)]
  · rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, zero_mul]
  · intro m _
    by_cases h1 : be ≤ m
    · rw [if_pos h1, coeff_monomial]
      by_cases h2 : m = μ + be
      · subst h2
        rw [if_pos (add_tsub_cancel_right μ be), if_pos rfl]
      · rw [if_neg h2, if_neg]
        intro h3
        apply h2
        rw [← h3, tsub_add_cancel_of_le h1]
    · rw [if_neg h1, coeff_zero, if_neg]
      rintro rfl
      exact h1 le_add_self
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
