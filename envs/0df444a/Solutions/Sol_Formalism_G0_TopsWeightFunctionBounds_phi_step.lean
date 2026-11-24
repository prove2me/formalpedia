-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.phi_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:34.193894+00:00
-- url     : https://prove2.me/submissions/1c153b45-b97d-4760-a0ef-769f626b9b23

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_d_le_one
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_aF_nonneg
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_gF_step
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_c_nonneg
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_phi_true

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
    (s : St) (hs : WF R s) :
    δ * Phi R L₂ δ (step R L₂ s true) + (1 - δ) * Phi R L₂ δ (step R L₂ s false) ≤ Phi R L₂ δ s := by
  have h1 := d_le_one h0 hL hLδ
  cases s with
  | bad => simp only [step, Phi]; linarith
  | good => simp only [step, Phi]; linarith
  | run K j d al ev =>
    simp only [WF] at hs
    have ht := phi_true h0 hL hLδ hR K j d al ev hs
    have hf : Phi R L₂ δ (step R L₂ (.run K j d al ev) false) =
        (1 - aF L₂ δ ^ R) ^ (K - 1) * (1 - GF R L₂ δ j (d + 1) al (!ev)) := by
      simp only [step, Phi]
    rw [hf]
    show _ ≤ (1 - aF L₂ δ ^ R) ^ (K - 1) * (1 - GF R L₂ δ j d al ev)
    have hC : 0 ≤ (1 - aF L₂ δ ^ R) ^ (K - 1) := pow_nonneg (c_nonneg h0 hLδ) _
    have hA : 0 ≤ aF L₂ δ ^ (R - 1 - j) := pow_nonneg (aF_nonneg hLδ) _
    cases al
    · simp only [GF, Bool.false_and, Bool.false_eq_true, if_false] at ht ⊢
      have e1 := mul_le_mul_of_nonneg_left ht h0
      nlinarith
    · simp only [GF, Bool.true_and, if_true] at ht ⊢
      have hg := gF_step (L₂ := L₂) h0 h1 j d ev
      have ho : (if okG L₂ j d ev = true then aF L₂ δ ^ (R - 1 - j) else 0) =
          aF L₂ δ ^ (R - 1 - j) * (if okG L₂ j d ev = true then (1 : ℝ) else 0) := by
        split_ifs <;> simp
      rw [ho] at ht
      have e1 := mul_le_mul_of_nonneg_left ht h0
      have e2 := mul_le_mul_of_nonneg_left hg (mul_nonneg hC hA)
      nlinarith [e1, e2]
end Formalism.G0.TopsWeightFunctionBounds
