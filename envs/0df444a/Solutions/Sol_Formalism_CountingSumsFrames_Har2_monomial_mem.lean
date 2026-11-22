-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.monomial_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:08.2361+00:00
-- url     : https://prove2.me/submissions/8d5cf29b-ae1f-403d-b347-241b96da256a

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
theorem _root_.solution {A B : ℕ} {m : XY k →₀ ℕ} (c : K) (hx : xDeg m = A) (hy : yDeg m = B) :
    monomial m c ∈ PolAB K k A B := by
  classical
  refine mem_PolAB_iff_forall_support_bidegree.2 fun m' hm' => ?_
  rw [Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hm')]
  exact ⟨hx, hy⟩
end Formalism.CountingSumsFrames.Har2
