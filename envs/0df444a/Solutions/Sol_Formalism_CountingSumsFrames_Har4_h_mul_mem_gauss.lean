-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.h_mul_mem_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:44.808381+00:00
-- url     : https://prove2.me/submissions/dc18a15a-0b99-44c2-8ad4-57fee4b29bc2

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
theorem _root_.solution {K : Type} [Field K] {k : ℕ} (R : Subring K) (G : PolXY K k) (hG : G ∈ GaussLat R) :
    hXY K k * G ∈ GaussLat R := by
  have hG' : ∀ m, coeff m G ∈ R := hG
  show ∀ m, coeff m (hXY K k * G) ∈ R
  intro m
  rw [MvPolynomial.coeff_mul]
  refine R.sum_mem fun x _ => R.mul_mem ?_ (hG' _)
  unfold hXY
  rw [MvPolynomial.coeff_sum]
  refine R.sum_mem fun i _ => ?_
  rw [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X']
  split_ifs <;> first | exact R.one_mem | exact R.zero_mem
end Formalism.CountingSumsFrames.Har4
