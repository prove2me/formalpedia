-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.hDiv_mem_PolAB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:45.071769+00:00
-- url     : https://prove2.me/submissions/a25cd0c2-dc4d-479a-bd74-0f3ff2c0e2e2

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_h_pow_mul_mem_PolAB

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
    hDiv K k l f ∈ PolAB K k (a + l) (b + l) := by
  unfold hDiv
  rw [LinearMap.smul_apply, LinearMap.mulLeft_apply]
  exact Submodule.smul_mem _ _ (h_pow_mul_mem_PolAB l hf)
end Formalism.CountingSumsFrames.Har4
