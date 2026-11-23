-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.ctrF_pow_mem_PolAB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:31.915277+00:00
-- url     : https://prove2.me/submissions/1d98b914-1238-48a1-8758-69243156e488

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_ctrF_mem_PolAB

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
    (ctrF K k ^ l) f ∈ PolAB K k (a - l) (b - l) := by
  induction l with
  | zero => simpa using hf
  | succ n ih =>
    rw [pow_succ']
    show ctrF K k ((ctrF K k ^ n) f) ∈ _
    have h := ctrF_mem_PolAB (K := K) ih
    convert h using 2 <;> omega
end Formalism.CountingSumsFrames.Har4
