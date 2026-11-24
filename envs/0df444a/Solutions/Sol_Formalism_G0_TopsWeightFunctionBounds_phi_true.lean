-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.phi_true
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:58.136268+00:00
-- url     : https://prove2.me/submissions/d689c00f-c59e-4275-a74f-6a12b3459831

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_aF_nonneg
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_gF_lb
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_c_nonneg
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Phi_init

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
    (K j d : ℕ) (al ev : Bool) (hj : j < R) :
    Phi R L₂ δ (step R L₂ (.run K j d al ev) true) ≤
      (1 - aF L₂ δ ^ R) ^ (K - 1) *
        (1 - (if (al && okG L₂ j d ev) = true then aF L₂ δ ^ (R - 1 - j) else 0)) := by
  have hC : 0 ≤ (1 - aF L₂ δ ^ R) ^ (K - 1) := pow_nonneg (c_nonneg h0 hLδ) _
  simp only [step]
  by_cases hjR : j + 1 = R
  · rw [if_pos hjR]
    have hA : aF L₂ δ ^ (R - 1 - j) = 1 := by rw [show R - 1 - j = 0 by omega, pow_zero]
    by_cases hg : (al && okG L₂ j d ev) = true
    · rw [if_pos hg, if_pos hg, hA]; simp [Phi]
    · rw [if_neg hg, if_neg hg]
      by_cases hK : K ≤ 1
      · rw [if_pos hK]; simp only [Phi]; rw [show K - 1 = 0 by omega]; simp
      · rw [if_neg hK, sub_zero, mul_one]
        have h := Phi_init (R := R) h0 hL hLδ hR (K := K - 1) (by omega) (!ev)
        exact h
  · rw [if_neg hjR]
    simp only [Phi]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold GF
    by_cases hg : (al && okG L₂ j d ev) = true
    · rw [if_pos hg, if_pos hg]
      have : aF L₂ δ ^ (R - 1 - j) ≤ aF L₂ δ ^ (R - 1 - (j + 1)) * gF L₂ δ (j + 1) 0 (!ev) := by
        calc aF L₂ δ ^ (R - 1 - j) = aF L₂ δ ^ (R - 1 - (j + 1)) * aF L₂ δ := by
              rw [← pow_succ]; congr 1; omega
          _ ≤ _ := mul_le_mul_of_nonneg_left (gF_lb h0 hL hLδ _ _) (pow_nonneg (aF_nonneg hLδ) _)
      linarith
    · rw [if_neg hg, if_neg hg]
end Formalism.G0.TopsWeightFunctionBounds
