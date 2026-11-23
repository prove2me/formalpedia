-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.divDer_single_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:59.421972+00:00
-- url     : https://prove2.me/submissions/c696c83a-aac9-4c80-8fa5-fe0a95957f06

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_coeff_divDer

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
theorem _root_.solution (v : ι × Fin n) (F : MvPolynomial (ι × Fin n) R) :
    divDer (Finsupp.single v 1) F = pderiv v F := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    ext μ
    rw [coeff_divDer, pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : u = μ + Finsupp.single v 1
    · subst h
      rw [if_pos rfl, if_pos (add_tsub_cancel_right μ _)]
      simp [Finsupp.prod_single_index, Nat.choose_one_right]
    · rw [if_neg h, zero_mul]
      split_ifs with h2
      · have hv : u v = 0 := by
          by_contra hv
          have hle : Finsupp.single v 1 ≤ u :=
            Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv)
          apply h
          rw [← h2, tsub_add_cancel_of_le hle]
        rw [hv, Nat.cast_zero, mul_zero]
      · rfl
  | add p q hp hq =>
    rw [map_add, ← hp, ← hq]
    ext μ
    rw [coeff_add, coeff_divDer, coeff_divDer, coeff_divDer, coeff_add, add_mul]
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
