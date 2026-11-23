-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.isotypicLattice_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:14.05324+00:00
-- url     : https://prove2.me/submissions/de0bb8a5-ab41-46f7-9df0-6a9d4be0cbf0

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_glAct_hXY
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_mem_latOf_iff
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_gaussLemmaPairing_holds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_h_pow_mul_mem_gauss

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
theorem _root_.solution : LevelLattice := by
  intro K _ _ k a b j O g hk
  ext f
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨hf, w, hw, rfl⟩
    exact ⟨w, ⟨gaussLemmaPairing_holds K k O g j w hk hf, hw⟩, rfl⟩
  · rintro ⟨w, ⟨hwl, hw⟩, rfl⟩
    refine ⟨?_, w, hw, rfl⟩
    rw [mem_latOf_iff] at hwl ⊢
    rw [map_mul, map_pow, glAct_hXY]
    exact h_pow_mul_mem_gauss O.toSubring j _ hwl
end Formalism.CountingSumsFrames.Har4
