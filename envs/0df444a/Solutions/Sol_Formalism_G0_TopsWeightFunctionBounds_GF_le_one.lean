-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.GF_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:15.1668+00:00
-- url     : https://prove2.me/submissions/80a1257f-c5fc-41c8-bbeb-8facaf7af5ab

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_d_le_one
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_gF_nonneg
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_gF_le_one__457661
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_aFpow_le

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
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (j d : ℕ) (al ev : Bool) :
    GF R L₂ δ j d al ev ≤ 1 := by
  have h1 := d_le_one h0 hL hLδ
  unfold GF; split_ifs
  · exact mul_le_one₀ (aFpow_le h0 hLδ _) (gF_nonneg h0 h1 _ _ _) (gF_le_one h0 h1 _ _ _)
  · norm_num
end Formalism.G0.TopsWeightFunctionBounds
