-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.hXY_mem_PolAB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:45.818009+00:00
-- url     : https://prove2.me/submissions/74525b47-fa54-478a-9f98-ca4f0731b9db

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
theorem _root_.solution : hXY K k ∈ PolAB K k 1 1 := by
  rw [mem_PolAB_iff]
  unfold hXY
  apply IsWeightedHomogeneous.sum
  intro i _
  have h := (isWeightedHomogeneous_X (R := K) (wXY k) (Sum.inl i)).mul
    (isWeightedHomogeneous_X (R := K) (wXY k) (Sum.inr i))
  convert h using 1
  simp [wXY]
end Formalism.CountingSumsFrames.Har4
