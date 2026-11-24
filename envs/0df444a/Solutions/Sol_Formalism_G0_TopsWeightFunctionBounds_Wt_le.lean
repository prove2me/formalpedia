-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.Wt_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:47.289829+00:00
-- url     : https://prove2.me/submissions/8d377ebb-9563-4186-b107-20de4b8528da

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_d_le_one
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Phi_nonneg
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_WF_step
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_phi_step

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
theorem _root_.solution (h0 : 0 ≤ δ) (hL : 1 ≤ L₂) (hLδ : (L₂ : ℝ) * δ ≤ 1) (hR : 1 ≤ R) (m : ℕ) :
    ∀ s, WF R s → Wt R L₂ δ m s ≤ Phi R L₂ δ s := by
  have h1 := d_le_one h0 hL hLδ
  induction m with
  | zero =>
    intro s hs
    simp only [Wt]
    split_ifs with h
    · subst h; simp [Phi]
    · exact Phi_nonneg h0 hL hLδ s
  | succ m ih =>
    intro s hs
    simp only [Wt]
    have a1 := ih _ (WF_step (L₂ := L₂) hR s hs true)
    have a2 := ih _ (WF_step (L₂ := L₂) hR s hs false)
    calc δ * Wt R L₂ δ m (step R L₂ s true) + (1 - δ) * Wt R L₂ δ m (step R L₂ s false)
        ≤ δ * Phi R L₂ δ (step R L₂ s true) + (1 - δ) * Phi R L₂ δ (step R L₂ s false) :=
          add_le_add (mul_le_mul_of_nonneg_left a1 h0) (mul_le_mul_of_nonneg_left a2 (by linarith))
      _ ≤ Phi R L₂ δ s := phi_step h0 hL hLδ hR s hs
end Formalism.G0.TopsWeightFunctionBounds
