-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.levelProj_mem_PolAB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:03.219658+00:00
-- url     : https://prove2.me/submissions/3cbb7af2-00bf-46eb-9b40-d7ddfb51bb27

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_ctrDiv_mem_PolAB
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_hDiv_mem_PolAB
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_harProj_mem_PolAB

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
theorem _root_.solution {A B j : ℕ} (hj : j ≤ min A B) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    levelProj K k A B j f ∈ PolAB K k A B := by
  unfold levelProj
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  simp only [LinearMap.comp_apply]
  have h := hDiv_mem_PolAB (K := K) j (harProj_mem_PolAB (ctrDiv_mem_PolAB j hf))
  have hA : A - j + j = A := Nat.sub_add_cancel (le_trans hj (min_le_left _ _))
  have hB : B - j + j = B := Nat.sub_add_cancel (le_trans hj (min_le_right _ _))
  rwa [hA, hB] at h
end Formalism.CountingSumsFrames.Har4
