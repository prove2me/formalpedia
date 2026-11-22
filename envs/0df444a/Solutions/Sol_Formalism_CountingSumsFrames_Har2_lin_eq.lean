-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.lin_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:22.891468+00:00
-- url     : https://prove2.me/submissions/6a0a71e4-ab1b-4482-91f7-068998a3a363

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
theorem _root_.solution {A B : ℕ} (T T' : PolXY K k →ₗ[K] PolXY K k)
    (h : ∀ (m : XY k →₀ ℕ) (c : K), xDeg m = A → yDeg m = B → T (monomial m c) = T' (monomial m c))
    {f : PolXY K k} (hf : f ∈ PolAB K k A B) : T f = T' f := by
  rw [MvPolynomial.as_sum f, map_sum, map_sum]
  exact Finset.sum_congr rfl fun m hm =>
    h m _ (mem_PolAB_iff_forall_support_bidegree.1 hf m hm).1 (mem_PolAB_iff_forall_support_bidegree.1 hf m hm).2
end Formalism.CountingSumsFrames.Har2
