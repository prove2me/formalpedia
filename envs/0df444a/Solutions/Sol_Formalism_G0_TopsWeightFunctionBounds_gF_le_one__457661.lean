-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.gF_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:30.396499+00:00
-- url     : https://prove2.me/submissions/5a4ea7d1-8616-4ec0-9c73-d90cb2febbe3

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_lo_le_hi
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_hi_le_one
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_lo_nonneg
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_eF_lb
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_eF_ub

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
theorem _root_.solution (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (j d : ℕ) (ev : Bool) : gF L₂ δ j d ev ≤ 1 := by
  unfold gF
  split_ifs
  · exact (lo_le_hi h0 h1).trans (hi_le_one h0 h1)
  · exact hi_le_one h0 h1
  · have hp : (1 - δ) ^ (L₂ / 2 - d) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have he := (eF_ub h0 h1 (max d (L₂ / 2))).trans (hi_le_one h0 h1)
    have he0 := (lo_nonneg h1).trans (eF_lb h0 h1 (max d (L₂ / 2)))
    calc (1 - δ) ^ (L₂ / 2 - d) * eF δ (max d (L₂ / 2)) ≤ 1 * 1 :=
          mul_le_mul hp he he0 zero_le_one
      _ = 1 := by ring
end Formalism.G0.TopsWeightFunctionBounds
