-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.lin_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:57.853593+00:00
-- url     : https://prove2.me/submissions/b323f368-e9f0-49b5-8a54-77936b910109

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
theorem _root_.solution {A B : ℕ} (T : PolXY K k →ₗ[K] PolXY K k) (S : Submodule K (PolXY K k))
    (h : ∀ (m : XY k →₀ ℕ) (c : K), xDeg m = A → yDeg m = B → T (monomial m c) ∈ S)
    {f : PolXY K k} (hf : f ∈ PolAB K k A B) : T f ∈ S := by
  rw [MvPolynomial.as_sum f, map_sum]
  exact Submodule.sum_mem _ fun m hm =>
    h m _ (mem_PolAB_iff_forall_support_bidegree.1 hf m hm).1 (mem_PolAB_iff_forall_support_bidegree.1 hf m hm).2
end Formalism.CountingSumsFrames.Har2
