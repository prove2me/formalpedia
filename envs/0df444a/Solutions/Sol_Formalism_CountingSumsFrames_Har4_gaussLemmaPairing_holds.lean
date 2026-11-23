-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.gaussLemmaPairing_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:31.057928+00:00
-- url     : https://prove2.me/submissions/f8eae674-55c6-42c4-b63c-11cafd2daa13

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_glAct_hXY
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_mem_latOf_iff
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_coeff_mem_of_h_pow_mul

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
theorem _root_.solution : GaussLemmaH := by
  intro K _ _ k O g j G hk h
  rw [mem_latOf_iff] at h ⊢
  rw [map_mul, map_pow, glAct_hXY] at h
  exact coeff_mem_of_h_pow_mul O.toSubring ⟨0, hk⟩ j _ h
end Formalism.CountingSumsFrames.Har4
