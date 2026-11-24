-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.gF_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:44.507906+00:00
-- url     : https://prove2.me/submissions/25e081a3-1a0b-4082-815e-6b8b5818241a

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_lo_le_hi
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_lo_nonneg
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_eF_lb

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
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {L₂ : ℕ} {δ : ℝ}
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j d : ℕ) (ev : Bool) : 0 ≤ gF L₂ δ j d ev := by
  unfold gF
  split_ifs
  · exact lo_nonneg h1
  · exact (lo_nonneg h1).trans (lo_le_hi h0 h1)
  · exact mul_nonneg (pow_nonneg (by linarith) _) ((lo_nonneg h1).trans (eF_lb h0 h1 _))
end Formalism.G0.TopsWeightFunctionBounds
