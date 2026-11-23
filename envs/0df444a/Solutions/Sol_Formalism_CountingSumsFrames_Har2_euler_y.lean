-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.euler_y
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:04.807226+00:00
-- url     : https://prove2.me/submissions/215057aa-9050-4ac3-83f6-3adb4be5764e

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
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
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
private theorem mem_PolAB_iff_forall_support_bidegree {A B : ℕ} {f : PolXY K k} :
    f ∈ PolAB K k A B ↔ ∀ m ∈ f.support, xDeg m = A ∧ yDeg m = B := Iff.rfl
private theorem X_mul_pderiv_monomialMultinomialDepth (v : XY k) (m : XY k →₀ ℕ) (c : K) :
    (X v : PolXY K k) * pderiv v (monomial m c) = monomial m (c * (m v : K)) := by
  rw [pderiv_monomial]
  by_cases h0 : m v = 0
  · simp only [h0, Nat.cast_zero, mul_zero, monomial_zero]
  · rw [show (X v : PolXY K k) = monomial (Finsupp.single v 1) 1 from rfl, monomial_mul, one_mul,
      add_tsub_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0))]
end Har2
open Har2
namespace Har2
variable {K : Type} [Field K] {k : ℕ}
end Har2
end Formalism.CountingSumsFrames
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ∑ i : Fin k, X (Sum.inr i) * pderiv (Sum.inr i) f = (B : K) • f := by
  have hf' := mem_PolAB_iff_forall_support_bidegree.1 hf
  conv_lhs => rw [MvPolynomial.as_sum f]
  conv_rhs => rw [MvPolynomial.as_sum f]
  simp only [map_sum, Finset.mul_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [X_mul_pderiv_monomialMultinomialDepth]
  rw [← map_sum (monomial m), ← Finset.mul_sum, ← Nat.cast_sum,
    show (∑ i : Fin k, m (Sum.inr i)) = B from (hf' m hm).2, smul_monomial, smul_eq_mul, mul_comm]
end Formalism.CountingSumsFrames.Har2
