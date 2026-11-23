-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.mul_mem_PolAB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:21.366308+00:00
-- url     : https://prove2.me/submissions/ad80941b-172e-4a2e-b2d9-b5e2a0d4d6bb

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_mem_PolAB_iff

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
theorem _root_.solution {a b a' b' : ℕ} {f f' : PolXY K k} (hf : f ∈ PolAB K k a b)
    (hf' : f' ∈ PolAB K k a' b') : f * f' ∈ PolAB K k (a + a') (b + b') := by
  rw [mem_PolAB_iff] at hf hf' ⊢
  simpa using hf.mul hf'
end Formalism.CountingSumsFrames.Har4
