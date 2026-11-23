-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.h_pow_mul_mem_PolAB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:19.772573+00:00
-- url     : https://prove2.me/submissions/9af38a3d-06e1-47f1-b009-e7e2f4835e8b

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_hXY_mem_PolAB
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_mul_mem_PolAB

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
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {a b : ℕ} (l : ℕ) {f : PolXY K k} (hf : f ∈ PolAB K k a b) :
    hXY K k ^ l * f ∈ PolAB K k (a + l) (b + l) := by
  induction l with
  | zero => simpa using hf
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    have h := mul_mem_PolAB hXY_mem_PolAB ih
    convert h using 2 <;> omega
end Formalism.CountingSumsFrames.Har4
