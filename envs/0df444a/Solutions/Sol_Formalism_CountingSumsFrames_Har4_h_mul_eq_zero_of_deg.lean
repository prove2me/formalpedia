-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.h_mul_eq_zero_of_deg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:40:56.136155+00:00
-- url     : https://prove2.me/submissions/84252f04-22c5-438c-8efa-d59ac22825ec

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {K : Type} [Field K] {k A B : ℕ} (hAB : A = 0 ∨ B = 0) {w G : PolXY K k}
    (hw : w ∈ PolAB K k A B) (h : w = hXY K k * G) : w = 0 := by
  subst h
  ext m
  rw [MvPolynomial.coeff_zero]
  by_cases h0 : coeff m (hXY K k * G) = 0
  · exact h0
  · obtain ⟨hx, hy⟩ := (show ∀ m ∈ (hXY K k * G).support, xDeg m = A ∧ yDeg m = B from hw) m
      (MvPolynomial.mem_support_iff.2 h0)
    unfold hXY
    rw [Finset.sum_mul, MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases hAB with hA | hB
    · have hle : m (Sum.inl i) ≤ xDeg m :=
        Finset.single_le_sum (f := fun j => m (Sum.inl j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hmi : m (Sum.inl i) = 0 := by omega
      rw [mul_assoc, MvPolynomial.coeff_X_mul', if_neg (by simpa [Finsupp.mem_support_iff] using hmi)]
    · have hle : m (Sum.inr i) ≤ yDeg m :=
        Finset.single_le_sum (f := fun j => m (Sum.inr j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hmi : m (Sum.inr i) = 0 := by omega
      rw [mul_comm (X (Sum.inl i)) (X (Sum.inr i)), mul_assoc, MvPolynomial.coeff_X_mul',
        if_neg (by simpa [Finsupp.mem_support_iff] using hmi)]
end Formalism.CountingSumsFrames.Har4
