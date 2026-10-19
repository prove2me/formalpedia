-- Prove2me | solution 2 for CohnElkies.saddleGaussian_fullLine_error_le_central_add_tails
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:20:35.458912+00:00
-- url     : https://prove2.me/submissions/9f186918-8fd8-40c9-b429-9988a363329f

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {F G : ℝ → ℂ}
    (hF : Integrable F) (hG : Integrable G)
    (R : ℝ) :
    ‖(∫ T : ℝ, F T) - (∫ T : ℝ, G T)‖ ≤
      ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ +
        (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) +
        (∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖) := by
  have hmT : MeasurableSet (saddleGaussianTailSet R) :=
    measurableSet_le measurable_const measurable_abs
  have hmI : MeasurableSet (Icc (-R) R) := measurableSet_Icc
  have hsub : (Icc (-R) R)ᶜ ⊆ saddleGaussianTailSet R := by
    intro T hT
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hT
    show R ≤ |T|
    rcases hT with h | h
    · linarith [neg_abs_le T]
    · linarith [le_abs_self T]
  have hF1 := integral_add_compl hmI hF
  have hG1 := integral_add_compl hmI hG
  have hFG : (∫ T in Icc (-R) R, (F T - G T)) = (∫ T in Icc (-R) R, F T) - ∫ T in Icc (-R) R, G T :=
    integral_sub hF.integrableOn hG.integrableOn
  have htF : ‖∫ T in (Icc (-R) R)ᶜ, F T‖ ≤ ∫ T in saddleGaussianTailSet R, ‖F T‖ :=
    (norm_integral_le_integral_norm _).trans
      (setIntegral_mono_set hF.norm.integrableOn (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall hsub))
  have htG : ‖∫ T in (Icc (-R) R)ᶜ, G T‖ ≤ ∫ T in saddleGaussianTailSet R, ‖G T‖ :=
    (norm_integral_le_integral_norm _).trans
      (setIntegral_mono_set hG.norm.integrableOn (Eventually.of_forall fun _ => norm_nonneg _)
        (Eventually.of_forall hsub))
  have heq : (∫ T, F T) - (∫ T, G T) = (∫ T in Icc (-R) R, (F T - G T)) +
      ((∫ T in (Icc (-R) R)ᶜ, F T) - ∫ T in (Icc (-R) R)ᶜ, G T) := by
    rw [hFG, ← hF1, ← hG1]; abel
  rw [heq]
  calc _ ≤ ‖∫ T in Icc (-R) R, (F T - G T)‖ + ‖(∫ T in (Icc (-R) R)ᶜ, F T) - ∫ T in (Icc (-R) R)ᶜ, G T‖ :=
        norm_add_le _ _
    _ ≤ ‖∫ T in Icc (-R) R, (F T - G T)‖ + (‖∫ T in (Icc (-R) R)ᶜ, F T‖ + ‖∫ T in (Icc (-R) R)ᶜ, G T‖) := by
        gcongr; exact norm_sub_le _ _
    _ ≤ _ := by linarith

