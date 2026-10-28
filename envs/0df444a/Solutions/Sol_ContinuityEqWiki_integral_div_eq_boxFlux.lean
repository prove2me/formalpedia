-- Prove2me | solution 1 for ContinuityEqWiki.integral_div_eq_boxFlux
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:14:17.459908+00:00
-- url     : https://prove2.me/submissions/ed6a59d9-d0aa-432f-875c-25374039716a

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

open ContinuityEqWiki

theorem solution (F : Space → Space) (hF : ContDiff ℝ 1 F)
    (a b : Space) (hab : a ≤ b) :
    ∫ x in Set.Icc a b, div F x = boxFlux F a b := by
  have hd : ∀ x, ∀ i : Fin 3, partialDeriv i (fun y => F y i) x = fderiv ℝ F x (Pi.single i 1) i := by
    intro x i
    unfold partialDeriv
    have h := (hF.differentiable one_ne_zero x).hasFDerivAt
    have h2 : HasFDerivAt ((fun v : Space => v i) ∘ F)
        ((ContinuousLinearMap.proj i).comp (fderiv ℝ F x)) x :=
      (hasFDerivAt_apply i (F x)).comp x h
    rw [show (fun y => F y i) = (fun v : Space => v i) ∘ F from rfl, h2.fderiv]
    rfl
  have hdiv : ∀ x, div F x = ∑ i, fderiv ℝ F x (Pi.single i 1) i := by
    intro x
    unfold div
    exact Finset.sum_congr rfl (fun i _ => hd x i)
  simp_rw [hdiv]
  unfold boxFlux
  have hcont : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  refine MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable a b hab F (fderiv ℝ F) ∅
    Set.countable_empty hF.continuous.continuousOn ?_ ?_
  · intro x _
    exact (hF.differentiable one_ne_zero x).hasFDerivAt
  · apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply Continuous.continuousOn
    apply continuous_finset_sum
    intro i _
    exact (continuous_apply i).comp (hcont.clm_apply continuous_const)
