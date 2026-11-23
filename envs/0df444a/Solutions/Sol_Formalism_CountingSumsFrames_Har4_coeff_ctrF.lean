-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.coeff_ctrF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:01.940465+00:00
-- url     : https://prove2.me/submissions/7fc3dd2f-806a-4947-8170-896d0cadf9e1

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
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.CountingSumsFrames
namespace Har4
section std
variable {K : Type} [Field K] [CharZero K] {k A B : ℕ} (R : Subring K)
end std
section deg
variable {K : Type} [Field K] {k : ℕ}
private theorem coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth (v : XY k) (F : PolXY K k) (m : XY k →₀ ℕ) :
    coeff m (pderiv v F) = coeff (m + Finsupp.single v 1) F * ((m v : K) + 1) := by
  refine MvPolynomial.induction_on' F ?_ ?_
  · intro s a
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hs : s = m + Finsupp.single v 1
    · subst hs
      simp
    · rw [if_neg hs, zero_mul]
      split_ifs with h
      · have hsv : s v = 0 := by
          by_contra hne
          apply hs
          rw [← h]
          ext u
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
          split_ifs with hu
          · subst hu
            omega
          · omega
        simp [hsv]
      · rfl
  · intro p q hp hq
    rw [map_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add, add_mul]
end deg
end Har4
end Formalism.CountingSumsFrames
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution (f : PolXY K k) (m : XY k →₀ ℕ) :
    coeff m (ctrF K k f) = ∑ i : Fin k,
      coeff (m + Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1) f *
        ((m (Sum.inr i) : K) + 1) * ((m (Sum.inl i) : K) + 1) := by
  unfold ctrF
  rw [LinearMap.sum_apply, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply]
  show coeff m (pderiv (R := K) (Sum.inl i : XY k) (pderiv (R := K) (Sum.inr i : XY k) f)) = _
  rw [coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth, coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth, Finsupp.add_apply, Finsupp.single_apply, if_neg Sum.inl_ne_inr,
    add_zero]
end Formalism.CountingSumsFrames.Har4
