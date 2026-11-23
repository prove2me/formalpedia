-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.sqrtFockGaussLatticeComparison_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:32.36555+00:00
-- url     : https://prove2.me/submissions/22b39234-3849-4f28-a8ad-ad5ece9d005e

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_mem_latOf_iff
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_glAct_mem_PolAB
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_sqrtFock_to_sqrtGauss
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_sqrtGauss_to_sqrtFock

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
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution : SqrtFockGaussXY := by
  intro K _ _ k A B p O g hk hp hR f hf
  have hf' : glAct g⁻¹ f ∈ PolAB K k A B := glAct_mem_PolAB g⁻¹ f hf
  constructor
  · intro h
    rw [mem_latOf_iff] at h ⊢
    exact sqrtFock_to_sqrtGauss O.toSubring hf' h
  · intro h
    rw [mem_latOf_iff] at h ⊢
    rw [map_smul]
    exact sqrtGauss_to_sqrtFock O.toSubring hp hR hf' h
end Formalism.CountingSumsFrames.Har4
