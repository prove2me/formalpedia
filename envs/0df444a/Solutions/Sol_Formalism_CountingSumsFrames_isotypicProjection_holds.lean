-- Prove2me | solution 1 for Formalism.CountingSumsFrames.isotypicProjection_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:53.300686+00:00
-- url     : https://prove2.me/submissions/b8702727-2c85-49f9-a6fc-7e6c594297fd

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_levelProj_image
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_levelProj_level
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_levelProj_sum

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
open Har2
namespace Formalism.CountingSumsFrames
theorem _root_.solution : LevelProj := by
  unfold LevelProj
  intro K _ _ k A B hk
  refine ⟨fun f hf j _ => levelProj_image hk j hf, fun f hf => levelProj_sum hk hf,
    fun f hf i hi j hj => ?_, fun i hi j hj w hw => levelProj_level hk hi hj hw⟩
  obtain ⟨w, hw, he⟩ := levelProj_image hk j hf
  rw [he, levelProj_level hk hj hi hw]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]
end Formalism.CountingSumsFrames
