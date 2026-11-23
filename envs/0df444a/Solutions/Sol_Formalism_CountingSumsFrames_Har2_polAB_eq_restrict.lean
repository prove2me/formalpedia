-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.polAB_eq_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:01.850796+00:00
-- url     : https://prove2.me/submissions/aed65f71-f6a4-4ebc-bccb-c9adbfc7073e

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
open Har2
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution (A B : ℕ) :
    PolAB K k A B = restrictSupport K {m : XY k →₀ ℕ | xDeg m = A ∧ yDeg m = B} := by
  ext f
  rw [mem_PolAB_iff_forall_support_bidegree, MvPolynomial.mem_restrictSupport_iff]
  exact ⟨fun h m hm => h m hm, fun h m hm => h hm⟩
end Formalism.CountingSumsFrames.Har2
