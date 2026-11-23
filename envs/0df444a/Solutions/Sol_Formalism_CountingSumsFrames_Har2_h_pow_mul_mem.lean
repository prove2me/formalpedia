-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.h_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:41.488502+00:00
-- url     : https://prove2.me/submissions/8115b13c-5bd8-4bde-a8c9-ad296cea5651

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_h_mul_mem

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
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution {A B : ℕ} (l : ℕ) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    hXY K k ^ l * f ∈ PolAB K k (A + l) (B + l) := by
  induction l with
  | zero => simpa using hf
  | succ l ih =>
    rw [pow_succ', mul_assoc, ← add_assoc, ← add_assoc]
    exact h_mul_mem ih
end Formalism.CountingSumsFrames.Har2
