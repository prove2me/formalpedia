-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.constants_of_theorem_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:48.536119+00:00
-- url     : https://prove2.me/submissions/9517d101-4ace-4dff-aabf-1532be404029

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelGrowthBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_level_recursion_lower_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_choice_of_constants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Real Formalism.FourierDecayAlt.P.LevelGrowthBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.TheoremAConstants := by
  intro C₁ CE C' C Θ Kx f r e a hC₁ hCE hf hK hC' hC hΘ' hΘ hr he ha hrec
  obtain ⟨_, q2, _, q4, q5⟩ :=
    choice_of_constants C₁ CE C' C Θ Kx f r hC₁ hCE hf hK hC' hC hΘ' hΘ hr
  have hΘ0 : 0 < Θ := by linarith
  have hδ0 : 0 ≤ (C₁ / Θ) ^ f := by positivity
  have hε0 : 0 ≤ (CE * Θ ^ (-(Kx - 5 / 2))) ^ f :=
    pow_nonneg (mul_nonneg hCE.le (Real.rpow_nonneg hΘ0.le _)) _
  have hLS := (level_recursion_lower_sum r ((CE * Θ ^ (-(Kx - 5 / 2))) ^ f) ((C₁ / Θ) ^ f) e a
    hε0 hδ0 (by linarith) he ha (by
      intro i h1 h2
      refine (hrec i h1 h2).trans (le_of_eq ?_)
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro s _
        rw [pow_mul]; ring)).2 q5
  have ha0 : 0 ≤ a 0 ^ 2 := sq_nonneg _
  have hprod : 0 ≤ ∏ i ∈ Icc 1 (r + 1), (1 + e i) :=
    Finset.prod_nonneg fun i _ => by linarith [he i]
  have hr1 : (0:ℝ) ≤ (r:ℝ) + 1 := by positivity
  refine hLS.trans ?_
  apply mul_le_mul_of_nonneg_right _ ha0
  apply mul_le_mul_of_nonneg_right _ hprod
  nlinarith [mul_le_mul_of_nonneg_left q4 hr1]
end Formalism.FourierDecayAlt.P
