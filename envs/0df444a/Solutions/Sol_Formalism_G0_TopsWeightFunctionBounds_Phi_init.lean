-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.Phi_init
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:23.363934+00:00
-- url     : https://prove2.me/submissions/d9d5797f-d94a-49a5-8904-27ccdac0906c

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_aF_nonneg
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_gF_lb
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_c_nonneg

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
theorem _root_.solution (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (hR : 1 ≤ R)
    {K : ℕ} (hK : 1 ≤ K) (ev : Bool) :
    Phi R L₂ δ (.run K 0 0 true ev) ≤ (1 - aF L₂ δ ^ R) ^ K := by
  simp only [Phi, GF, if_true, Nat.sub_zero]
  have hg := gF_lb h0 hL hLδ 0 ev
  have hle : aF L₂ δ ^ R ≤ aF L₂ δ ^ (R - 1) * gF L₂ δ 0 0 ev := by
    calc aF L₂ δ ^ R = aF L₂ δ ^ (R - 1) * aF L₂ δ := by
          rw [← pow_succ]; congr 1; omega
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (pow_nonneg (aF_nonneg hLδ) _)
  calc (1 - aF L₂ δ ^ R) ^ (K - 1) * (1 - aF L₂ δ ^ (R - 1) * gF L₂ δ 0 0 ev)
        ≤ (1 - aF L₂ δ ^ R) ^ (K - 1) * (1 - aF L₂ δ ^ R) :=
          mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (c_nonneg h0 hLδ) _)
    _ = (1 - aF L₂ δ ^ R) ^ K := by rw [← pow_succ, Nat.sub_add_cancel hK]
end Formalism.G0.TopsWeightFunctionBounds
