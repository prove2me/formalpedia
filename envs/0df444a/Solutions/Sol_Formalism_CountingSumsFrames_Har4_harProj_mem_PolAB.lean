-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.harProj_mem_PolAB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:04:19.990252+00:00
-- url     : https://prove2.me/submissions/d6a7d924-89b8-4dfb-9b01-a0deea360d7b

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_ctrDiv_mem_PolAB
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_hDiv_mem_PolAB

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
theorem _root_.solution {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    harProj K k A B f ∈ PolAB K k A B := by
  unfold harProj
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l hl => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply]
  refine Submodule.smul_mem _ _ ?_
  have hl' : l ≤ min A B := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  have h := hDiv_mem_PolAB (K := K) l (ctrDiv_mem_PolAB (K := K) l hf)
  rwa [Nat.sub_add_cancel (le_trans hl' (min_le_left _ _)),
    Nat.sub_add_cancel (le_trans hl' (min_le_right _ _))] at h
end Formalism.CountingSumsFrames.Har4
